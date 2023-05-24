
pub mod mirai_check_that_fails {

    use crate::mock::TemplateModule;
    use crate::mock::RuntimeOrigin;

    pub struct SabineTest {

    }

    impl SabineTest {
        pub fn false_precon(&self) {
            //precondition!(false);
            self.second_fun();
        }

        pub fn second_fun(&self) {
            precondition!(false);
        }
    }

    pub fn test_failure() {
        // let origin = RuntimeOrigin::signed(1);
        let _ = TemplateModule::do_something_non_pallet();
        // verify!(false);
        // let s = SabineTest{};
        // s.false_precon();
        // s.second_fun();
    }
}