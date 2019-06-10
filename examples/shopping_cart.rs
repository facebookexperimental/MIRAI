#![feature(type_alias_enum_variants)]

#[macro_use]
extern crate mirai_annotations;

pub mod foreign_contracts;

struct Cart {
    /// We model a shopping cart as Vector of items.
    /// We are interested in the cost of those items
    /// for checkout purposes so we only add the items'
    /// cost (as an u32) to the cart.
    items: Vec<u32>,
}

impl Cart {
    fn new() -> Cart {
        Cart { items: Vec::new() }
    }

    fn add_item(&mut self, value: u32) {
        // We don't want items with zero
        // value to be added to the cart
        precondition!(value > 0);
        self.items.push(value);
    }

    fn remove_item(&mut self) -> Option<u32> {
        self.items.pop()
    }

    fn num_items(&self) -> usize {
        self.items.len()
    }

    fn checkout(&self) -> u32 {
        let mut sum: u32 = 0;
        let len = self.items.len();
        let mut i = 0;
        while i < len {
            let x = self.items.get(i);
            match x {
                None => {}
                Some(item) => {
                    sum = sum + *item;
                }
            }
            i += 1;
        }
        // We check the following condition: Either the
        // cart is empty or the sum value of the items
        // in the cart is non-negative.
        verify!(len == 0 || sum > 0);
        sum
    }
}

fn main() {
    let mut cart = Cart::new();

    cart.add_item(10);
    let _ = cart.remove_item();

    cart.add_item(20);
    cart.add_item(30);
    cart.add_item(40);
    let item_count = cart.num_items();
    let total = cart.checkout();

    // We check that the cart's total value
    // is greater than zero, as we would expect
    // for a non-empty cart.
    verify!(total > 0);

    println!("Item count: {} | Total price: {}", item_count, total);
}
