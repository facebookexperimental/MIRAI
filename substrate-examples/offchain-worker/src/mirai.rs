


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

//pub mod mirai_check_that_fails {
    //use crate::mirai::SecretTaint;
    use frame_support::pallet_prelude::*;
    use crate::Pallet;
    use crate::tests::Test;

    #[test]
    pub fn test_failure() {

        //let call = pallet::Call::<Runtime>::foo_no_post_info {};
        //let call = Call::bench_call { transfer: Default::default() };
        //let call = Call::submit_price_unsigned { block_number, price };
        let call: crate::Call<Test> = crate::Call::submit_price_unsigned {
            block_number: 1,
            price: 15523
        };
        /*let call = crate::Call::submit_price_unsigned {
            block_number: 1,
            price: 15523
        };*/
        //let call = Pallet::create_call();

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
//}