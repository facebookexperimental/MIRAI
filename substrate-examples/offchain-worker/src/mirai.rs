#[cfg(mirai)]
use mirai_annotations::{TagPropagation, TagPropagationSet};

#[cfg(mirai)]
struct SecretTaintKind<const MASK: TagPropagationSet> {}

#[cfg(mirai)]
const SECRET_TAINT_MASK: TagPropagationSet = tag_propagation_set!(TagPropagation::SubComponent);

#[cfg(mirai)]
type SecretTaint = SecretTaintKind<SECRET_TAINT_MASK>;
#[cfg(not(mirai))]
type SecretTaint = ();

use crate::tests::Test;
use crate::Pallet;
use frame_support::pallet_prelude::*;

#[test]
pub fn test_failure() {
    let call: crate::Call<Test> = crate::Call::submit_price_unsigned {
        block_number: 1,
        price: 15523,
    };

    let validity = Pallet::validate_unsigned(TransactionSource::Local, &call).unwrap_err();

    let s: String = "Hello World".to_string();
    //verify_data(&s);
    dangerous_stuff(&s);
    //verify!(false);
}

fn verify_data(s: &String) {
    add_tag!(s, SecretTaint);
}

fn dangerous_stuff(s: &String) {
    precondition!(has_tag!(s, SecretTaint));
}
