use radguy::{kleene_local, oracle::SMax};

mod bislotmap;
mod systems;

fn main() {
    let mut sys = bool_system! {
        x = (y || x);
        y = z;
        z = tt;
    };
    sys.print_definitions();

    let start = sys.names.get_or_insert_key("x");
    let oracle = SMax;
    println!("{}", kleene_local(&sys, start, &oracle));
}
