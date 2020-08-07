pub fn main() {
    let a = 5;
    assume!(a < 5); //this assumption is provably false and it will be ignored
    verify!(a == 5);
}
