use radguy::{extension::ExtensionOracle, kleene_local};
use slotmap::DefaultKey;

use crate::systems::bool::extension::BoolExtension;

mod bislotmap;
mod systems;

fn main() {
    let mut sys = bool_system! {
        x = (x || y);
        y = z;
        z = tt;
    };
    sys.print_definitions();

    let start = sys.names.get_or_insert_key("x");
    let ext = BoolExtension::<DefaultKey>::default();
    let oracle = ExtensionOracle::from(ext);
    println!("{}", kleene_local(&sys, start, &oracle));
}
