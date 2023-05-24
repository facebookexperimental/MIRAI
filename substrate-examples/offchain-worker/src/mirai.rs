pub mod mirai_check_that_fails {

    pub fn test_failure() {
        verify!(false);
    }
}