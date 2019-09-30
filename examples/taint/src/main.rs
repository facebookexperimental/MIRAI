extern crate taint_error;
use std::sync::Arc;
use taint_error::{source, use_arc, Foo};
fn use_arc_test() {
    let f: Foo = source(Arc::new([1, 2, 3])); // get tainted Foo
    let (_, sum) = use_arc(f); // use tainted Foo
    println!("sum = {}", sum);
}

fn main() {
    use_arc_test();
}
