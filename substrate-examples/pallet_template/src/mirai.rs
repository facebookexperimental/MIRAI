
pub mod mirai_check_that_fails {

    use crate::mock::TemplateModule;
    use crate::mock::RuntimeOrigin;

    pub fn test_failure() {
        let origin = RuntimeOrigin::signed(1);
        let _ = TemplateModule::do_something(origin, 42);
        verify!(false);
    }
}