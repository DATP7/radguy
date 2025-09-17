mod bislotmap;
mod systems;

fn main() {
    let sys = bool_system! {
        x = (x || y);
        y = z;
        z = tt;
    };
    dbg!(sys);
}
