
pub mod mirai_check_that_fails {

    use crate::mock::TemplateModule;
    use crate::mock::RuntimeOrigin;

    pub fn test_failure() {
        let _ = TemplateModule::do_something(RuntimeOrigin::signed(1), 42);
    }
}