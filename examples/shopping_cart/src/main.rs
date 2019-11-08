// This is an example of using pre/post conditions as well as invariants
// via the contracts crate.
//
// We define a simple shopping cart with an invariant both on items in the cart
// and the overall cart.
//
// TODO(wrwg): this example is not yet fully functional regarding MIRAI verification.
use contracts::*;

use mirai_annotations::*;

// Items stored in the shopping cart.
pub struct Item {
    // TODO(wrwg): make this String once supported
    name: &'static str,
    price: u64,
}

impl Item {
    // Invariant for the Item struct. We define those invariants via functions
    // so they can easily be referenced from attributes.
    fn invariant(&self) -> bool {
        !self.name.is_empty() && self.price > 0
    }

    // Creates a new Item, satisfying the invariant. Notice we can't use
    // the `#[invariant]` attribute for new because this requires a `self` argument.
    #[pre(!name.is_empty() && price > 0)]
    #[post(ret.invariant())]
    fn new(name: &'static str, price: u64) -> Item {
        Item { name, price }
    }
}

// The shopping cart, consisting of a list of items, and the total price for
// all the items in the cart.
pub struct ShoppingCart {
    items: Vec<Item>,
    total: u64,
}

impl ShoppingCart {
    // Invariant for the shopping cart.
    fn invariant(&self) -> bool {
        // TODO(wrwg): this invariant is currently not handled by MIRAI:
        // function DefId(2:1711 ~ core[5a18]::ops[0]::deref[0]::Deref[0]::deref[0])
        // Comment the code out to see other issues with this code.
        self.items.iter().all(|x| x.invariant())
            && self.items.iter().map(|x| x.price).sum::<u64>() == self.total
    }

    #[post(ret.invariant())]
    fn new() -> ShoppingCart {
        ShoppingCart {
            items: vec![],
            total: 0,
        }
    }
}

// Implements methods of the shopping cart. By attaching the `#[invariant]` attribute
// all methods in the impl which work on `self` get automatically injected
// the invariant both as pre and post condition, in addition to what they state
// individually.
// TODO(wrwg): having both an invariant here and a post below is currently not supported
// by MIRAI: "only one post condition is supported"
#[invariant(self.invariant())]
impl ShoppingCart {
    #[post(self.items.len() == old(self.items.len()) + 1)]
    fn add(&mut self, item: Item) {
        self.total += item.price;
        self.items.push(item);
    }

    // TODO(wrwg): This seems to generate a false positive:
    // "provably false verification condition" (after warning for
    // integer overflow, which might be the cause).
    #[post(self.items.len() == old(self.items.len()) + 1)]
    fn add_broken_invariant(&mut self, item: Item) {
        //self.total += item.price;
        self.items.push(item);
    }

    // TODO(wrwg): This currently can not be handled by MIRAI:
    // DefId(2:1739 ~ core[5a18]::ops[0]::function[0]::FnMut[0]::call_mut[0])
    #[post(ret == old(self.total))]
    fn checkout(&mut self) -> u64 {
        let bill = self.total;
        self.total = 0;
        self.items.clear();
        bill
    }
}

// A main entry point which violates conditions.
pub fn main() {
    let mut cart = ShoppingCart::new();
    // The below should fail because pre-condition of Item::new is violated.
    cart.add(Item::new("free lunch", 0));
    checked_verify!(cart.checkout() == 0);
}

#[cfg(test)]
mod tests {
    use mirai_annotations::*;

    use crate::{Item, ShoppingCart};

    #[test]
    fn ok() {
        let mut cart = ShoppingCart::new();
        cart.add(Item::new("ipad pro", 899));
        cart.add(Item::new("ipad folio", 169));
        checked_verify_eq!(cart.checkout(), 899 + 169);
    }

    #[test]
    #[should_panic(expected = "Pre-condition of new violated")]
    fn fail_item_new() {
        let mut cart = ShoppingCart::new();
        // Below violates precondition of Item::new
        cart.add(Item::new("free lunch", 0));
        checked_verify_eq!(cart.checkout(), 0);
    }

    #[test]
    #[should_panic(expected = "Invariant of add_broken_invariant violated")]
    fn fail_add_invariant() {
        let mut cart = ShoppingCart::new();
        cart.add_broken_invariant(Item::new("ipad pro", 899));
        checked_verify_eq!(cart.checkout(), 899);
    }
}
