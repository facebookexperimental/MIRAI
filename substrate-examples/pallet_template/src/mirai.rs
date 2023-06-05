pub mod mirai_check {

    use crate::mock::RuntimeOrigin;
    use crate::mock::TemplateModule;

    pub fn code_to_analyze() {
        let _ = TemplateModule::do_something(RuntimeOrigin::signed(1), 42);
    }
}
