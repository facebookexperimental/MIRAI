# MIRAI Standard Contracts

This crate provides a set of function definitions that provide summaries of parts of the Rust standard library.

Until such time as the standard library is annotated for MIRAI, this provides a place for such annotations.

The crate is not intended to be used by any other crate. Instead, MIRAI will run over this crate and produce a
corresponding database for summaries. This database will be bundled with the MIRAI binary and
will be used as the seed for the database created for a project analyzed by MIRAI.