// Copyright (c) Facebook, Inc. and its affiliates.
//
// This source code is licensed under the MIT license found in the
// LICENSE file in the root directory of this source tree.
//

#[derive(Debug)]
pub enum Error {
    InputFailed,
    ParseFailed,
    UnknownValue,
}

#[derive(Debug)]
pub enum NonZeroEnum {
    One = 1,
    Two = 2,
    Three = 3,
}

impl NonZeroEnum {
    pub fn try_from_optional(source: u8) -> Result<Option<Self>, Error> {
        match source {
            0 => Ok(None),
            1 => Ok(Some(NonZeroEnum::One)),
            2 => Ok(Some(NonZeroEnum::Two)),
            3 => Ok(Some(NonZeroEnum::Three)),
            _ => Err(Error::UnknownValue),
        }
    }
}

pub fn main() {}
