
pub mod mirai_check_that_fails {

    pub fn test_failure() {
        // System::set_block_number(1);
        verify!(false);
    }
}