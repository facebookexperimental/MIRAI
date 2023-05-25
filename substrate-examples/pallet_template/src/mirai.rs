
pub mod mirai_check {

    use crate::mock::TemplateModule;
    use crate::mock::RuntimeOrigin;

    pub fn code_to_analyze() {
        let _ = TemplateModule::do_something(RuntimeOrigin::signed(1), 42);
    }
}