use mirai_annotations::*;

fn main() {
    call(1);
}

fn call(x: i32) {
    checked_assume!(x > 0);
    let f = || {
        // The below should not be needed and inferred from the context, but it does not
        // work (uncomment to reproduce)
        checked_assume!(x > 0);
        checked_verify!(x > 0);
    };
    f()
}
