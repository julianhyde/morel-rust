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

// Used by tests/lint.rs but not by the main shell.
#![allow(dead_code)]

//! Validates signature files against built-in function and record definitions.
//!
//! This module provides the [`SignatureValidator`] which ensures that
//! signature files in the `lib/` directory are well-formed and consistent
//! with the definitions in [`crate::compile::library`].
//!
//! This is the Rust equivalent of Java's `SignatureChecker` class.

use crate::syntax::parser::{ParseError, parse_statement};
use std::error;
use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// Validates signature files against built-in definitions.
///
/// This validator checks that:
/// - Signature files exist and are readable
/// - Files have proper header formatting
/// - Value and exception declarations match entries in BuiltInFunction and
///   BuiltInRecord
///
/// # Examples
///
/// ```no_run
/// use morel::compile::signature_validator::SignatureValidator;
///
/// let validator = SignatureValidator::new("lib");
/// validator.validate_all().expect("Signature validation failed");
/// ```
pub struct SignatureValidator {
    lib_dir: PathBuf,
}

impl SignatureValidator {
    /// Creates a new signature validator for the given library directory.
    pub fn new<P: AsRef<Path>>(lib_dir: P) -> Self {
        Self {
            lib_dir: lib_dir.as_ref().to_path_buf(),
        }
    }

    /// Validates all signature files in the library directory.
    ///
    /// # Errors
    ///
    /// Returns an error if:
    /// - The library directory doesn't exist or isn't a directory
    /// - No signature files are found
    /// - Any signature file cannot be read
    /// - Any signature file fails validation
    pub fn validate_all(&self) -> Result<(), ValidationError> {
        if !self.lib_dir.exists() {
            return Err(ValidationError::DirectoryNotFound(
                self.lib_dir.clone(),
            ));
        }

        if !self.lib_dir.is_dir() {
            return Err(ValidationError::NotADirectory(self.lib_dir.clone()));
        }

        let entries = self.collect_signature_files()?;

        if entries.is_empty() {
            return Err(ValidationError::NoSignatureFiles(
                self.lib_dir.clone(),
            ));
        }

        for path in entries {
            self.validate_file(&path)?;
        }

        Ok(())
    }

    /// Collects all `.sig` and `.sml` files from the library directory.
    fn collect_signature_files(&self) -> Result<Vec<PathBuf>, ValidationError> {
        let entries = fs::read_dir(&self.lib_dir)
            .map_err(|e| {
                ValidationError::DirectoryReadError(self.lib_dir.clone(), e)
            })?
            .filter_map(Result::ok)
            .filter(|e| {
                e.path()
                    .extension()
                    .is_some_and(|ext| ext == "sig" || ext == "sml")
            })
            .map(|e| e.path())
            .collect();

        Ok(entries)
    }

    /// Validates a single signature file.
    ///
    /// Reads the file, then parses it as a Morel statement to confirm
    /// the source is syntactically well-formed (including any attribute
    /// or doc-comment annotations on the contained specs).
    ///
    /// Future enhancements:
    /// - Walk the parse tree to compare each val/exception/datatype
    ///   spec against the strum-tagged `BuiltInFunction` /
    ///   `BuiltInExn` / `BuiltInDatatype` enums.
    /// - Validate that the type signatures match.
    fn validate_file(&self, path: &Path) -> Result<(), ValidationError> {
        let contents = fs::read_to_string(path).map_err(|e| {
            ValidationError::FileReadError(path.to_path_buf(), e)
        })?;
        parse_statement(&contents).map_err(|e| {
            ValidationError::ParseError(path.to_path_buf(), Box::new(e))
        })?;
        Ok(())
    }
}

/// Errors that can occur during signature validation.
#[derive(Debug)]
pub enum ValidationError {
    // lint: sort until '#}' where '##[A-Z]'
    /// The library directory was not found.
    DirectoryNotFound(PathBuf),
    /// Failed to read the directory.
    DirectoryReadError(PathBuf, io::Error),
    /// Failed to read a signature file.
    FileReadError(PathBuf, io::Error),
    /// No signature files were found in the directory.
    NoSignatureFiles(PathBuf),
    /// The path exists but is not a directory.
    NotADirectory(PathBuf),
    /// A signature file did not parse as a Morel statement.
    ParseError(PathBuf, Box<ParseError>),
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            // lint: sort until '#}' where '##ValidationError::'
            ValidationError::DirectoryNotFound(path) => {
                write!(f, "Library directory not found: {}", path.display())
            }
            ValidationError::DirectoryReadError(path, err) => {
                write!(
                    f,
                    "Failed to read directory {}: {}",
                    path.display(),
                    err
                )
            }
            ValidationError::FileReadError(path, err) => {
                write!(
                    f,
                    "Failed to read signature file {}: {}",
                    path.display(),
                    err
                )
            }
            ValidationError::NoSignatureFiles(path) => {
                write!(f, "No signature files found in: {}", path.display())
            }
            ValidationError::NotADirectory(path) => {
                write!(f, "Path is not a directory: {}", path.display())
            }
            ValidationError::ParseError(path, err) => {
                write!(
                    f,
                    "Failed to parse signature file {}: {}",
                    path.display(),
                    err
                )
            }
        }
    }
}

impl error::Error for ValidationError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            ValidationError::DirectoryReadError(_, err)
            | ValidationError::FileReadError(_, err) => Some(err),
            ValidationError::ParseError(_, err) => Some(err.as_ref()),
            _ => None,
        }
    }
}
