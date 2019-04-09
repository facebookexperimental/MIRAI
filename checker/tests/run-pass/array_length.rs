#![feature(box_syntax)]

#[macro_use]
extern crate mirai_annotations;

pub enum Path {
    QualifiedPath { length: usize, qualifier: Box<Path> },
    Root,
}

impl Path {
    pub fn path_length(&self) -> usize {
        match self {
            Path::QualifiedPath { length, .. } => *length,
            _ => 1,
        }
    }

    pub fn replace_root(&self, new_root: Path) -> Path {
        match self {
            Path::QualifiedPath { qualifier, .. } => {
                checked_assume!(qualifier.path_length() <= 10);
                Path::QualifiedPath {
                    length: qualifier.path_length() + 1,
                    qualifier: box Path::Root,
                }
            }
            _ => new_root,
        }
    }
}

pub fn main() {}
