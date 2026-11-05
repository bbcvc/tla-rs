//! The order `set_order` gives symbols. It's process-wide, so these tests run in their own
//! process and one at a time.

use std::sync::Mutex;

use tla_tools_intern::{Symbol, set_order};

static ORDER: Mutex<()> = Mutex::new(());

#[test]
fn ranks_the_given_texts_first() {
    let _order = ORDER.lock().unwrap();
    let early = Symbol::intern("order-early");
    let late = Symbol::intern("order-late");
    assert!(early < late);
    set_order(["order-late", "order-new", "order-late"]);
    let new = Symbol::get("order-new").expect("set_order interns its texts");
    assert!(late < new && new < early);
    assert_eq!((late.rank(), new.rank(), early.rank()), (Some(0), Some(1), None));
    let fresh = Symbol::intern("order-fresh");
    assert!(early < fresh, "unranked symbols keep the order of interning");
    let mut sorted = vec![fresh, early, new, late];
    sorted.sort();
    assert_eq!(sorted, [late, new, early, fresh]);
}

#[test]
fn replaces_an_earlier_order() {
    let _order = ORDER.lock().unwrap();
    set_order(["replace-b", "replace-a"]);
    let (a, b) = (Symbol::intern("replace-a"), Symbol::intern("replace-b"));
    assert!(b < a);
    set_order(["replace-a"]);
    assert!(a < b);
    assert_eq!(b.rank(), None);
}
