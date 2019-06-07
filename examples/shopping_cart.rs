#![feature(type_alias_enum_variants)]

#[macro_use]
extern crate mirai_annotations;

pub mod foreign_contracts;

struct Cart {
    items: Vec<i32>
}

impl Cart {
    fn new() -> Cart {
        Cart {
            items: Vec::new(),
        }
    }

    fn add_item(&mut self, value: i32) {
        precondition!(value > 0);
        let old_len = self.items.len();
        self.items.push(value);
        verify!(self.items.len() == old_len + 1);
    }

    fn remove_item(&mut self) -> Option<i32> {
        let old_len = self.items.len();
        let res = self.items.pop();
        verify!(self.items.len() == 0 || self.items.len() == old_len - 1);
        res
    }

    fn num_items(&self) -> usize {
        self.items.len()
    }

    fn checkout(&self) -> i32 {
        let mut sum: i32 = 0;
        let len = self.items.len();
        let mut i = 0;
        while i < len {
            let x = self.items.get(i);
            match x {
                None => {},
                Some(item) => {
                    sum = sum + *item;
                }
            }
            i += 1;
        }
        verify!(len <= 0 || sum > 0);
        sum
    }
}

fn main() {
    let mut cart = Cart::new(); 

    let old_num_items = cart.num_items();
    cart.add_item(10);
    verify!(cart.num_items() == old_num_items + 1);
    let _ = cart.remove_item();
    verify!(cart.num_items() == old_num_items);

    cart.add_item(20);
    cart.add_item(30);
    cart.add_item(40);
    let total = cart.checkout();
    verify!(total > 0);

    println!("Total: {}", total);
}
