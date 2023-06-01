

pub mod mirai_check_that_fails {
    use frame_support::pallet_prelude::*;
    use crate::Pallet;
    use crate::tests::Test;

    pub fn test_failure() {
        let call: crate::Call<Test> = crate::Call::submit_price_unsigned {
            block_number: 1,
            price: 15523,
        };

        let validity = Pallet::validate_unsigned(TransactionSource::Local, &call).unwrap_err();
    }
}