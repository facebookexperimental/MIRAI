# Proof of Concept: Tag Analysis on Origin

This is a copy of [substrate's pallet template](https://github.com/substrate-developer-hub/substrate-node-template/tree/e0c480c0f322d0b0d1b310c93fa646fc0cfdd2df/pallets/template), enriched with a MIRAI [tag-analysis](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/TagAnalysis.md). It is a first proof-of-concept for a [detection of unchecked origins](https://github.com/bhargavbh/MIRAI/blob/main/substrate_examples/incorrect-origin/description.md).

# Running

To run the analysis [install mirai]() and run

`cargo mirai`

from within this folder. The [config.toml](.cargo/config.toml) makes sure, that the analysis only runs on the function [`mirai_check.code_to_analyze`](src/mirai.rs).

# Tag Analysis
We use [tag analysis](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/TagAnalysis.md) from MIRAI. In this example, we want to verify that `ensure_signed` is called on the `origin`, before the storage is set. We implemented two wrapper functions to accomplish this:

First, we add a tag to `tagged_value` before `ensure_signed` is called:

``` rust
fn sarp_ensure_signed(origin: OriginFor<T>, tagged_value: &u32) -> Result<T::AccountId, BadOrigin> {
    add_tag!(tagged_value, SecretTaint);
    ensure_signed(origin.clone())
}
```

Then, for writing the storage, we added a precondition, that `tagged_value` has a tag:

``` rust
fn sarp_put_sensitive_value(origin: OriginFor<T>, something: u32, tagged_value: &u32) -> DispatchResult {
	precondition!(has_tag!(tagged_value, SecretTaint));
	<Something<T>>::put(something);
	Ok(())
}
```

To try out both cases, the following two lines can be un-/commented:

``` rust
// switch between the next two lines to either get a precondition failure in sarp_put_sensitive_value or not
let who = Self::sarp_ensure_signed(origin.clone(), &tagged_value)?;
// let who = ensure_signed(origin.clone())?;
```

## Open issues
- tag the `origin` and not an additional variable `tagged_value`. Tagging the `origin` has not given the expected results so far, but would be important to really track if `ensure_signed` has been called on the specific `origin`.
- There seems to be an issue, with nesting `precondition!` and `verify!` inside functions. Although the problem could not be reproduced with the examples from the MIRAI repository. When nested inside a function we have to set `--diag=paranoid`, whereas when they are not nested a `--diag=verify` is sufficient (and results in much fewer warnings).

## Output

