#![feature(type_alias_enum_variants)]

#[macro_use]
extern crate mirai_annotations;

pub mod foreign_contracts;

fn add_item(cart: &mut Vec<i32>, value: i32) {
    cart.push(value);
}

fn remove_item(cart: &mut Vec<i32>) -> Option<i32> {
    cart.pop()
}

fn main() {
    let mut cart: Vec<i32> = Vec::new();
    let old_len = cart.len();
    add_item(&mut cart, 10);
    verify!(cart.len() == old_len + 1);
    let _ = remove_item(&mut cart);
    verify!(cart.len() == old_len);
}
