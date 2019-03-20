// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::path::{Path, PathBuf};
use std::str::FromStr;
use syntax::errors::Diagnostic;

/// A collection of error strings that are expected for a test case.
pub struct ExpectedErrors {
    messages: Vec<String>,
}

impl ExpectedErrors {
    /// Reads the file at the given path and scans it for instances of "//~ message".
    /// Each message becomes an element of ExpectedErrors.messages.
    pub fn new(path: &str) -> ExpectedErrors {
        let exp = load_errors(&PathBuf::from_str(&path).unwrap());
        ExpectedErrors { messages: exp }
    }

    /// Checks if the given set of diagnostics matches the expected diagnostics.
    pub fn check_messages(&mut self, diagnostics: Vec<Diagnostic>) {
        diagnostics.iter().for_each(|diag| {
            self.remove_message(&diag.message());
            for child in &diag.children {
                self.remove_message(&child.message());
            }
        });
        if !self.messages.is_empty() {
            panic!("Expected errors not reported: {:?}", self.messages);
        }
    }

    /// Removes the first element of self.messages and checks if it matches msg.
    fn remove_message(&mut self, msg: &str) {
        if self.messages.remove_item(&String::from(msg)).is_none() {
            panic!("Unexpected error: {} Expected: {:?}", msg, self.messages);
        }
    }
}

/// Scans the contents of test file for patterns of the form "//~ message"
/// and returns a vector of the matching messages.
fn load_errors(testfile: &Path) -> Vec<String> {
    let rdr = BufReader::new(File::open(testfile).unwrap());
    let tag = "//~";
    rdr.lines()
        .enumerate()
        .filter_map(|(_line_num, line)| parse_expected(&line.unwrap(), &tag))
        .collect()
}

/// Returns the message part of the pattern "//~ message" if there is a match, otherwise None.
fn parse_expected(line: &str, tag: &str) -> Option<String> {
    let start = line.find(tag)? + tag.len();
    Some(String::from(line[start..].trim()))
}
