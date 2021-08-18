// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.

// MIRAI_FLAGS --diag=default

pub enum DebugCommand {
    Breakpoint(String),
}

impl DebugCommand {
    pub fn debug_string(&self) -> &str {
        match self {
            Self::Breakpoint(_) => "breakpoint ",
        }
    }

    pub fn commands() -> Vec<DebugCommand> {
        vec![Self::Breakpoint("".to_string())]
    }

    // pub fn join_commands() -> String {
    //     Self::commands()
    //         .iter()
    //         .map(|command| command.debug_string())
    //         .collect::<Vec<_>>()
    //         .join(", ")
    // }
}

pub fn main() {}
