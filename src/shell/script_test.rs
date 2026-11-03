// Licensed to Julian Hyde under one or more contributor license
// agreements.  See the NOTICE file distributed with this work
// for additional information regarding copyright ownership.
// Julian Hyde licenses this file to you under the Apache
// License, Version 2.0 (the "License"); you may not use this
// file except in compliance with the License.  You may obtain a
// copy of the License at
//
// http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND,
// either express or implied.  See the License for the specific
// language governing permissions and limitations under the
// License.

use crate::eval::session::Config as SessionConfig;
use crate::eval::spark;
use crate::eval::val::Val;
use crate::shell::config::Config;
use crate::shell::error::Error;
use crate::shell::{Kernel, ScriptRunner, ShellResult, utils};
use crate::spark as spark_adapter;
use std::env::{self, temp_dir};
use std::fs::{self};
use std::path::{Path, PathBuf};
use std::rc::Rc;

/// Environment variable that, when set, says that a live Spark Connect
/// server is available, at the URI that `SPARK_REMOTE` names. The
/// analog of morel-java's system property `morel.spark`.
pub const MOREL_SPARK: &str = "MOREL_SPARK";

/// Returns the URI of the live Spark Connect server, if there is one:
/// `MOREL_SPARK` is set, and `SPARK_REMOTE` names the server.
pub fn spark_uri() -> Option<String> {
    env::var_os(MOREL_SPARK)?;
    env::var(spark::SPARK_REMOTE)
        .ok()
        .filter(|uri| !uri.is_empty())
}

/// Returns whether a `requires:` condition holds, or an error if the
/// condition is unknown.
///
/// The conditions are those of morel-java's harness: `spark-adapter`
/// (the Spark adapter is present), `no-spark-adapter` (it is not),
/// `spark` (a live Spark Connect server, which the harness binds as
/// `spark`; see [`spark_uri`]), and `spark-prepare` (the `Spark`
/// structure has `prepare`). The adapter is present in a native build,
/// so there `spark-adapter` holds and `no-spark-adapter` does not.
pub fn holds(condition: &str) -> ShellResult<bool> {
    match condition {
        "spark-prepare" => Ok(true),
        "spark-adapter" => Ok(spark_adapter::is_available()),
        "no-spark-adapter" => Ok(!spark_adapter::is_available()),
        "spark" => Ok(spark_adapter::is_available() && spark_uri().is_some()),
        _ => Err(Error::Runtime(format!(
            "unknown condition '{}' in requires directive",
            condition
        ))),
    }
}

/// Returns the conditions of a script's `(*) requires:` directives.
///
/// A script whose header has a line `(*) requires: <conditions>` runs
/// only when every condition, separated by spaces, holds.
fn requirements(in_file: &Path) -> Vec<String> {
    let Ok(contents) = fs::read_to_string(in_file) else {
        return Vec::new();
    };
    contents
        .lines()
        .take(40)
        .filter_map(|line| line.strip_prefix("(*) requires: "))
        .flat_map(|conditions| conditions.split_whitespace())
        .map(str::to_string)
        .collect()
}

/// Test runner for script files, equivalent to Java ScriptTest.
pub struct ScriptTest {
    config: SessionConfig,
    /// Whether to run every query on Spark; see
    /// [`Self::with_spark_push_down`].
    spark_push_down: bool,
}

impl ScriptTest {
    /// Creates a ScriptTest.
    pub fn new(config: SessionConfig) -> Self {
        Self {
            config,
            spark_push_down: false,
        }
    }

    /// Returns a copy of this runner that runs every query on Spark.
    ///
    /// It sets the `sparkPushDown` property, which is what a session
    /// sets to the same end, so that each query is wrapped in
    /// `Spark.remote` and sent to the connection bound as `spark`, which
    /// the runner binds to the live server; and it clears
    /// `sparkFallback`, so that a query Spark cannot do fails rather than
    /// being answered here. The output goes beside the local run's, with
    /// the suffix `.spark`.
    #[allow(dead_code)] // used by the tests, not by the binary
    pub fn with_spark_push_down(self) -> Self {
        Self {
            spark_push_down: true,
            ..self
        }
    }

    /// Gets the test directory.
    pub fn directory(&self) -> Option<&Path> {
        match &self.config.directory {
            None => None,
            Some(d) => Some(d.as_path()),
        }
    }

    /// Runs a single test file.
    pub fn run<P: AsRef<Path>>(&self, path: P) -> ShellResult<()> {
        let path = path.as_ref();
        let (in_file, out_file) = self.resolve_files(path)?;

        // A script that requires what this build lacks is skipped, and
        // passes.
        let conditions = requirements(&in_file);
        for condition in &conditions {
            if !holds(condition)? {
                eprintln!(
                    "{} skipped: requires {}",
                    in_file.display(),
                    condition
                );
                return Ok(());
            }
        }
        // A script that needs a live server is given a connection to it,
        // bound as `spark`, as `Spark.connect` would return it; and so
        // is a script whose queries all run there.
        let bind_spark =
            self.spark_push_down || conditions.iter().any(|c| c == "spark");
        let spark_uri = if bind_spark { spark_uri() } else { None };
        if bind_spark && spark_uri.is_none() {
            eprintln!("{} skipped: requires spark", in_file.display());
            return Ok(());
        }
        let out_file = if self.spark_push_down {
            PathBuf::from(format!("{}.spark", out_file.display()))
        } else {
            out_file
        };

        // Determine if this is an idempotent test (*.smli files)
        let idempotent = path.to_string_lossy().ends_with(".smli")
            || path.to_str() == Some("-");

        // Create the output directory if needed
        if let Some(parent) = out_file.parent() {
            fs::create_dir_all(parent)?;
        }

        // Set up configuration. Both script modes echo input lines (so the
        // output file contains the full transcript); neither writes '- '
        // prompts (those are only for interactive use). The difference is
        // that idempotent mode prefixes result lines with '> '.
        let shell_config = Config {
            echo: Some(true),
            banner: Some(false),
            idempotent: Some(idempotent),
            prompt: Some(false),
            stdin_is_tty: Some(false),
            ..Config::default()
        };

        let mut session_config = SessionConfig::default();
        if let Some(script_dir) = in_file.parent().map(Path::to_path_buf) {
            // Walk up from the script's directory until we find an ancestor
            // named "script"; the directory that contains it (e.g. `tests/`)
            // becomes the base directory used to resolve `.input` files.
            // Mirrors morel-java's Script.run().
            let mut directory = script_dir.clone();
            let mut cursor: Option<&Path> = Some(script_dir.as_path());
            while let Some(d) = cursor {
                if d.file_name().is_some_and(|n| n == "script") {
                    if let Some(parent) = d.parent() {
                        directory = parent.to_path_buf();
                    }
                    break;
                }
                cursor = d.parent();
            }
            // For the "file.smli" test, move to a subdirectory; it's
            // more predictable.
            let path_str = path.to_string_lossy();
            if path_str.contains("/file.") {
                directory.push("data");
            }
            session_config.script_directory = Some(Rc::new(script_dir));
            session_config.directory = Some(Rc::new(directory));
        }

        // Create and run the shell
        let mut shell = Kernel::with_config(shell_config);

        // Apply session config (script directory, etc.)
        shell.apply_session_config(&session_config);

        let mut connection = None;
        if let Some(uri) = &spark_uri {
            let bind = format!("val spark = Spark.connect \"{}\"", uri);
            shell.process_statement(&bind, None)?;
            if let Some(Val::Progressive(record)) = shell.get_val("spark")
                && let Ok(Some(Val::Connection(c))) =
                    record.field_value("connection")
            {
                connection = Some(c);
            }
            if self.spark_push_down {
                shell.process_statement(
                    "Sys.set (\"sparkPushDown\", true)",
                    None,
                )?;
                shell.process_statement(
                    "Sys.set (\"sparkFallback\", false)",
                    None,
                )?;
            }
        }

        // Run the input file and capture output
        let mut output = Vec::new();
        let result =
            ScriptRunner::new(&mut shell).run_file(&in_file, &mut output);
        // The script may have bound `spark` to something else; close the
        // connection the harness made, whatever it is called now.
        if let Some(c) = connection {
            c.close();
        }
        result?;

        // Write output to file
        fs::write(&out_file, &output)?;

        // Compare with reference file
        let ref_file = if idempotent {
            in_file.clone()
        } else {
            let mut ref_path = in_file.clone();
            ref_path.set_extension(format!(
                "{}.out",
                ref_path.extension().and_then(|s| s.to_str()).unwrap_or("")
            ));
            ref_path
        };

        if !ref_file.exists() {
            eprintln!("Reference file not found: {}", ref_file.display());
            return Ok(());
        }

        // Compare files
        let diff = utils::diff_files(&ref_file, &out_file)?;
        if !diff.is_empty() {
            return Err(Error::Runtime(format!(
                "Files differ: {} {}\n{}",
                ref_file.display(),
                out_file.display(),
                diff
            )));
        }

        Ok(())
    }

    /// Resolves input and output file paths.
    fn resolve_files(&self, path: &Path) -> ShellResult<(PathBuf, PathBuf)> {
        let path_str = path.to_string_lossy();

        if path_str == "-" {
            // Special case for stdin
            let in_file = temp_dir().join("morel-stdin.smli");
            let out_file = temp_dir().join("morel-stdin.smli.out");
            return Ok((in_file, out_file));
        }

        if path.is_absolute() {
            // Absolute path
            let in_file = path.to_path_buf();
            let out_file = PathBuf::from(format!("{}.out", path.display()));
            return Ok((in_file, out_file));
        }

        if let Some(dir) = &self.directory() {
            // Relative to the specified directory
            let in_file = dir.join(path);
            let out_file = dir.join(format!("{}.out", path.display()));
            return Ok((in_file, out_file));
        }

        // Default: look in resources (for now, just use relative path)
        let in_file = PathBuf::from(path);
        let out_file = PathBuf::from("target/test-output")
            .join(format!("{}.out", path.display()));

        Ok((in_file, out_file))
    }

    /// Gets all test files in the script directory.
    pub fn find_test_files(&self) -> ShellResult<Vec<PathBuf>> {
        let script_dir = self.directory().as_ref().map_or_else(
            || PathBuf::from("src/test/resources/script"),
            |d| d.join("script"),
        );

        if !script_dir.exists() {
            return Ok(Vec::new());
        }

        let mut files = Vec::new();
        for entry in fs::read_dir(script_dir)? {
            let entry = entry?;
            let path = entry.path();

            if let Some(ext) = path.extension()
                && (ext == "sml" || ext == "smli")
            {
                files.push(path);
            }
        }

        files.sort();
        Ok(files)
    }

    /// Runs all tests in the script directory.
    pub fn run_all_tests(&self) -> ShellResult<()> {
        let test_files = self.find_test_files()?;
        let mut failed_tests = Vec::new();

        for file in &test_files {
            println!("Running test: {}", file.display());

            match self.run(file) {
                Ok(()) => {
                    println!("  PASSED");
                }
                Err(e) => {
                    println!("  FAILED: {}", e);
                    failed_tests.push(file.clone());
                }
            }
        }

        if failed_tests.is_empty() {
            println!("All {} tests passed!", test_files.len());
            Ok(())
        } else {
            println!(
                "{} out of {} tests failed:",
                failed_tests.len(),
                test_files.len()
            );
            for file in &failed_tests {
                println!("  {}", file.display());
            }
            Err(Error::Runtime(format!(
                "{} tests failed",
                failed_tests.len()
            )))
        }
    }

    /// Main entry point for command-line usage.
    pub fn main(args: &[String]) -> ShellResult<()> {
        let mut test_files = Vec::new();
        let mut config = SessionConfig::default();

        // Parse arguments
        for arg in args {
            if let Some(dir) = arg.strip_prefix("--directory=") {
                config.directory = Some(Rc::new(PathBuf::from(dir)));
            } else if !arg.starts_with("--") {
                test_files.push(PathBuf::from(arg));
            }
        }

        let script_test = ScriptTest::new(config);

        if test_files.is_empty() {
            // Run all tests
            script_test.run_all_tests()
        } else {
            // Run specific tests
            let mut failed = false;
            for file in test_files {
                match script_test.run(&file) {
                    Ok(()) => {
                        println!("PASSED: {}", file.display());
                    }
                    Err(e) => {
                        println!("FAILED: {}: {}", file.display(), e);
                        failed = true;
                    }
                }
            }

            if failed {
                Err(Error::Runtime("Some tests failed".to_string()))
            } else {
                Ok(())
            }
        }
    }
}

impl Default for ScriptTest {
    fn default() -> Self {
        Self::new(SessionConfig::default())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_script_test_creation() {
        let st = ScriptTest::default();
        assert_eq!(st.directory(), None);

        let mut config = SessionConfig::default();
        config.directory = Some(Rc::new(PathBuf::from("/tmp")));
        let st = ScriptTest::new(config);
        assert_eq!(st.directory(), Some(Path::new("/tmp")));
    }

    #[test]
    fn test_resolve_files() {
        let st = ScriptTest::default();
        let (in_file, out_file) =
            st.resolve_files(Path::new("test.sml")).unwrap();

        assert!(in_file.to_string_lossy().contains("test.sml"));
        assert!(out_file.to_string_lossy().contains("test.sml.out"));
    }

    #[test]
    fn test_find_test_files() {
        let st = ScriptTest::default();
        // This test will depend on actual test files being present
        let files = st.find_test_files().unwrap_or_default();
        // Just verify it doesn't crash
        println!("Found {} test files", files.len());
    }
}
