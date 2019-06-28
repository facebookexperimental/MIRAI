# Troubleshooting

## Missing contracts
Running MIRAI with log level set to `info` (`MIRAI_LOG=info`) gives information on missing contracts with the 
message `Summary store has no entry for ...`.
Add this missing contract to the file `standard_contracts/src/foreign_contracts.rs` and execute the script `rebuild_std.sh`.
This is applicable to missing contracts for functions in the Rust standard library. If it is for another crate, 
that crate should either be analyzed with MIRAI or foreign contracts should be added to the crate.

## Types of missing contracts
`rustc <rust_src>.rs -Zunpretty=mir` has information on the parameter and return types of missing contracts. 