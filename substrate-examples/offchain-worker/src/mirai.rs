

pub mod mirai_check {
    use frame_support::pallet_prelude::*;
    use crate::Pallet;
    use crate::tests::Test;
    use crate::SubmitTransaction;
    use frame_system::offchain::Signer;
    use frame_system::offchain::SendUnsignedTransaction;

    pub fn code_to_analyze(block_number: u64, price: u32) {
        let call: crate::Call<Test> = crate::Call::submit_price_unsigned {
            block_number: block_number,
            price: price,
        };

        let validity = Pallet::validate_unsigned(TransactionSource::Local, &call).unwrap_err();
    }

    pub fn submit_unsigned_transaction(block_number: u64, price: u32) {
        let call: crate::Call<Test> = crate::Call::submit_price_unsigned {
            block_number: block_number,
            price: price,
        };

        SubmitTransaction::<Test, crate::Call<Test>>::submit_unsigned_transaction(call.into());
    }
}