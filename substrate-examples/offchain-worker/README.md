# Proof of Concept: Tag Analysis on Origin

This is a copy of [substrate's pallet template](https://github.com/substrate-developer-hub/substrate-node-template/tree/e0c480c0f322d0b0d1b310c93fa646fc0cfdd2df/pallets/template), enriched with a MIRAI [tag-analysis](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/TagAnalysis.md). It is a first proof-of-concept for a [validation of unsigned transactions](https://github.com/bhargavbh/MIRAI/blob/main/substrate_examples/unsigned-transaction/description.md).

# Running

To run the analysis [install mirai](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/InstallationGuide.md) and run

`cargo mirai`

from within this folder. The [config.toml](.cargo/config.toml) makes sure, that the analysis only runs on the function [`mirai_check.code_to_analyze`](src/mirai.rs).

# Tag Analysis
We use [tag analysis](https://github.com/facebookexperimental/MIRAI/blob/main/documentation/TagAnalysis.md) from MIRAI. In this example, we want to verify that all parameters are properly verified before we call `transform_data`. The tags are set in `validate_transaction_parameters` once the parameters pass the validation:
``` rust
    let current_block = <system::Pallet<T>>::block_number();
    if &current_block < block_number {
        return InvalidTransaction::Future.into()
    }
    add_tag!(block_number, ParameterVerified);
    
    // Arbitrary check that price is bigger than some value
    if 100 > *new_price {
        return InvalidTransaction::Future.into()
    }
    add_tag!(new_price, ParameterVerified);
```

The `transform_data` function is currently not doing anything but it requires that the two parameters have the `ParameterVerified` tag:

``` rust
    #[requires(has_tag!(new_price, ParameterVerified))]
    #[requires(has_tag!(block_number, ParameterVerified))]
    fn transform_data(
        block_number: &T::BlockNumber,
        new_price: &u32,
    ) {

    }
```

## Output

In one case `transform_data` is called without considering the return value of `validate_transaction_parameters` and because of that MIRAI is raising an issue about an unsatisfied precondition:
``` rust
    let res = Self::validate_transaction_parameters(block_number, new_price);
    // Applying the data without properly checking that the parameters were validated correctly
    Self::transform_data(block_number, new_price);
```
In the other use case the return type is considered and therefore there are no warnings:
``` rust
    // Properly check that the transaction is valid before applying the data
    if res.is_ok() {
        Self::transform_data(&payload.block_number, &payload.price);
    }
```


There is a warning, when the tag is not added:

![Output_Unsatisfied_Precondition](UnsatisfiedPrecondition.png)


## Open issues

- One specific piece of code lead to a crash in MIRAI
- For more complex scenarios timeouts arise within MIRAI. In some cases increasing the `body_analysis_timeout` parameter leads to crashes in MIRAI.
- There are a variety of other warnings raised from code in other crates. This is confusing to the user.
