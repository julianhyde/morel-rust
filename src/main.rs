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

extern crate core;
use crate::shell::{ScriptTest, Shell as ShellMain};
use std::io::{stdin, stdout};
use std::process::exit;

mod compile;
mod eval;
mod shell;
mod syntax;
mod unify;

fn print_help() {
    println!("morel-rust version {}", env!("CARGO_PKG_VERSION"));
    println!();
    println!("Usage: morel [OPTIONS] [FILES...]");
    println!("       morel -c COMMAND");
    println!("       morel test [FILES...]");
    println!("       morel -h | --help");
    println!();
    println!("Options:");
    println!("  -h, --help         Print this help message and exit");
    println!("  -c COMMAND         Execute a single command and exit");
    println!(
        "  --idempotent       Force idempotent mode for all files and stdin"
    );
    println!(
        "  --no-idempotent    Force non-idempotent mode for all files / stdin"
    );
    println!("  --directory=DIR    Set the working directory");
    println!(
        "  --                 End of options; remaining args are file names"
    );
    println!();
    println!("Arguments:");
    println!(
        "  FILES...           Morel script files to run. Use '-' for stdin."
    );
    println!("                     With no files (and no --idempotent/");
    println!(
        "                     --no-idempotent), an interactive REPL reads"
    );
    println!("                     from standard input.");
    println!();
    println!("Modes:");
    println!(
        "  By default, each file runs in idempotent mode if its suffix is"
    );
    println!(
        "  '.smli', otherwise in normal (transcript) mode. --idempotent /"
    );
    println!("  --no-idempotent override the per-file default.");
    println!();
    println!("  Idempotent mode: echoes input and prefixes results with '> '.");
    println!(
        "  Output reproduces the .smli test-file format (round-trip-safe)."
    );
    println!();
    println!(
        "  Normal mode: echoes input only (no '> ' prefix); a transcript."
    );
    println!();
    println!("Examples:");
    println!("  morel                         Interactive REPL");
    println!("  morel -c \"1 + 2\"              Execute a single command");
    println!("  morel script.sml              Run script, transcript mode");
    println!("  morel script.smli             Run script, idempotent mode");
    println!(
        "  morel a.sml b.smli            Run two scripts (mode per suffix)"
    );
    println!("  morel --idempotent < file     Run stdin in idempotent mode");
    println!("  morel --no-idempotent x.smli  Override suffix rule");
    println!("  morel test [files...]         Run script tests");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Quick dispatch for special subcommands.
    if args.len() > 1 {
        match args[1].as_str() {
            "-h" | "--help" => {
                print_help();
                exit(0);
            }
            "test" => {
                let test_args = args[2..].to_vec();
                match ScriptTest::main(&test_args) {
                    Ok(()) => {
                        println!("All tests completed successfully");
                        exit(0);
                    }
                    Err(e) => {
                        eprintln!("Test error: {}", e);
                        exit(1);
                    }
                }
            }
            "-c" => {
                if args.len() < 3 {
                    eprintln!("-c requires a command argument");
                    exit(1);
                }
                let command = &args[2];
                let mut main = ShellMain::new(&[]);
                match main.run_command(command, stdout()) {
                    Ok(()) => exit(0),
                    Err(e) => {
                        eprintln!("Error executing command: {}", e);
                        exit(1);
                    }
                }
            }
            _ => {}
        }
    }

    // Parse flags and files. Flags may be interleaved with files; a bare
    // '--' ends flag parsing.
    let mut force_idempotent: Option<bool> = None;
    let mut directory: Option<String> = None;
    let mut files: Vec<String> = Vec::new();
    let mut end_of_flags = false;
    for arg in &args[1..] {
        if end_of_flags {
            files.push(arg.clone());
            continue;
        }
        match arg.as_str() {
            "--" => end_of_flags = true,
            "--idempotent" => force_idempotent = Some(true),
            "--no-idempotent" => force_idempotent = Some(false),
            _ if arg.starts_with("--directory=") => {
                directory =
                    Some(arg.strip_prefix("--directory=").unwrap().to_string());
            }
            _ if arg.starts_with("--") => {
                eprintln!("Unknown option: {}", arg);
                exit(1);
            }
            _ => files.push(arg.clone()),
        }
    }

    if files.is_empty() && force_idempotent.is_none() {
        run_interactive(directory.as_deref());
    } else {
        if files.is_empty() {
            files.push("-".to_string());
        }
        run_scripts(&files, force_idempotent, directory.as_deref());
    }
}

fn run_interactive(directory: Option<&str>) {
    let mut shell_args = vec!["--prompt".to_string(), "--banner".to_string()];
    if std::io::IsTerminal::is_terminal(&stdin()) {
        shell_args.push("--tty".to_string());
    }
    if let Some(dir) = directory {
        shell_args.push(format!("--directory={}", dir));
    }
    let mut main = ShellMain::new(&shell_args);
    match main.run(stdin(), stdout()) {
        Ok(()) => {
            println!("Goodbye!");
        }
        Err(e) => {
            eprintln!("Shell error: {}", e);
            exit(1);
        }
    }
}

fn run_scripts(
    files: &[String],
    force_idempotent: Option<bool>,
    directory: Option<&str>,
) {
    let mut shell_args: Vec<String> = Vec::new();
    if let Some(dir) = directory {
        shell_args.push(format!("--directory={}", dir));
    }
    let mut shell = ShellMain::new(&shell_args);
    // Script mode: no banner, no prompts, echo input lines (transcript).
    shell.config.banner = Some(false);
    shell.config.prompt = Some(false);
    shell.config.stdin_is_tty = Some(false);
    shell.config.echo = Some(true);

    for file in files {
        let idempotent = match force_idempotent {
            Some(force) => force,
            None => file.ends_with(".smli"),
        };
        shell.config.idempotent = Some(idempotent);

        let result = if file == "-" {
            shell.run(stdin(), stdout())
        } else {
            shell.run_file(file, stdout())
        };
        if let Err(e) = result {
            eprintln!("Error running {}: {}", file, e);
            exit(1);
        }
    }
    exit(0);
}

#[cfg(test)]
mod test {
    #[test]
    fn test_dummy() {
        // Placeholder test to ensure tests still run
        assert_eq!(2 + 2, 4);
    }
}
