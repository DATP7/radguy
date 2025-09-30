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

#[cfg(test)]
mod tests {
    use paste::paste;
    use radguy::oracle::TrivialOracle;

    use super::*;

    macro_rules! test_oracle {
        ($name:ident) => {
            paste! {
                #[test]
                fn [<test_kleene_local_$name:lower _system>]() {
                    let oracle = $name;
                    let mut sys = bool_system! {
                        x = (((y || z) && k) || j);
                        y = ((x || j) || (z && k));
                        z = (((a || b) || (c && d)) || ((e || f) && (g && h))) ;
                        k = tt;
                        j = (j || j);
                        a = j;
                        b = a;
                        c = k;
                        d = b;
                        e = c;
                        f = d;
                        g = e;
                        h = g;
                    };
                    let var_vector = ["x", "y", "z", "k", "j", "a", "b", "c", "d", "e", "f", "g"];
                    let goal_vector = [true, true, true, true, false, false, false, true, false, true, false, true, true];
                    for (var, goal) in var_vector.into_iter().zip(goal_vector.into_iter()) {
                        let start = sys.names.get_or_insert_key(var);
                        assert_eq!(kleene_local(&sys, start, &oracle), goal);
                    }
                }
            }
        };
    }
    macro_rules! test_bool_value {
        (tt) => {
            #[test]
            fn test_kleene_local_smax_tt() {
                let oracle = SMax;
                let mut sys = bool_system! {
                    x = tt;
                };
                let start = sys.names.get_or_insert_key("x");
                assert_eq!(kleene_local(&sys, start, &oracle), true);
            }
        };
        (ff) => {
            #[test]
            fn test_kleene_local_smax_ff() {
                let oracle = SMax;
                let mut sys = bool_system! {
                    x = ff;
                };
                let start = sys.names.get_or_insert_key("x");
                assert_eq!(kleene_local(&sys, start, &oracle), false);
            }
        };
    }

    macro_rules! test_oracles {
        ( $( $name:ident ),*) => {
            $(
                test_oracle!($name);
            )*
        };
    }
    macro_rules! test_bool_values {
        ( $( $name:ident ),*) => {
            $(
                test_bool_value!($name);
            )*
        };
    }

    test_bool_values!(tt, ff);

    #[test]
    fn test_kleene_local_smax_and() {
        let oracle = SMax;
        let mut sys1 = bool_system! {
            x = (y && z);
            y = tt;
            z = tt;
        };
        let start1 = sys1.names.get_or_insert_key("x");
        assert_eq!(kleene_local(&sys1, start1, &oracle), true);

        let mut sys2: systems::bool::BoolSystem<slotmap::DefaultKey, slotmap::DefaultKey> = bool_system! {
            x =(y && z);
            y = tt;
            z = ff;
        };
        let start2 = sys2.names.get_or_insert_key("x");
        assert_eq!(kleene_local(&sys2, start2, &oracle), false);
        let mut sys3 = bool_system! {
            x =(y && z);
            y = ff;
            z = ff;
        };
        let start3 = sys3.names.get_or_insert_key("x");
        assert_eq!(kleene_local(&sys3, start3, &oracle), false);
    }
    #[test]
    fn test_kleene_local_smax_or() {
        let oracle = SMax;
        let mut sys1: systems::bool::BoolSystem<slotmap::DefaultKey, slotmap::DefaultKey> = bool_system! {
            x =(y || z);
            y = tt;
            z = tt;
        };
        let start1 = sys1.names.get_or_insert_key("x");
        assert_eq!(kleene_local(&sys1, start1, &oracle), true);
        let mut sys2 = bool_system! {
            x =(y || z);
            y = tt;
            z = ff;
        };
        let start2 = sys2.names.get_or_insert_key("x");
        assert_eq!(kleene_local(&sys2, start2, &oracle), true);
        let mut sys3 = bool_system! {
            x =(y || z);
            y = ff;
            z = ff;
        };
        let start3 = sys3.names.get_or_insert_key("x");
        assert_eq!(kleene_local(&sys3, start3, &oracle), false);
    }
    #[test]
    fn test_kleene_local_smax_parentheses() {
        let mut sys1 = bool_system! {
            x = ((y || z) && (k || j));
            y = ff;
            z = ff;
            k = tt;
            j = tt;
        };
        let start1 = sys1.names.get_or_insert_key("x");
        let oracle = SMax;
        assert_eq!(kleene_local(&sys1, start1, &oracle), false);

        let mut sys2 = bool_system! {
            x = (((y || z) && k) || j);
            y = ff;
            z = ff;
            k = tt;
            j = tt;
        };
        let start2 = sys2.names.get_or_insert_key("x");
        assert_eq!(kleene_local(&sys2, start2, &oracle), true);
        assert_ne!(
            kleene_local(&sys1, start1, &oracle),
            kleene_local(&sys2, start2, &oracle)
        );
    }

    test_oracles!(SMax, TrivialOracle);
}
