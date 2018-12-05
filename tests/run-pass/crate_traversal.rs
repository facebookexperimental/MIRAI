// A small trait to test crate traversal

trait TestTrait {
    fn test_method() {}
}

struct TestStruct {
     test_field: i64
}

impl TestStruct {
    fn test_function() {}
    fn test_method(&self) {}
}

fn main() {}
