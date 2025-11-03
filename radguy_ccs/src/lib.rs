pub mod systems;

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use radguy::kleene_local;
    use radguy::oracle::{LocalMaxR, LocalOracle, SMax, TrivialOracle};
    use slotmap::DefaultKey;

    use crate::systems::bool::BoolSystem;

    use super::*;

    fn test_system() -> (
        BoolSystem<DefaultKey, DefaultKey, &'static str>,
        [&'static str; 13],
        [bool; 13],
    ) {
        let sys = bool_system! {
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
        let var_vector = [
            "x", "y", "z", "k", "j", "a", "b", "c", "d", "e", "f", "g", "h",
        ];
        let goal_vector = [
            true, true, true, true, false, false, false, true, false, true, false, true, true,
        ];
        (sys, var_vector, goal_vector)
    }

    macro_rules! test_oracle {
        ($oracle:expr, $name:ident) => {
            #[test]
            fn $name() {
                let (mut sys, var_vector, goal_vector) = test_system();
                for (var, goal) in var_vector.into_iter().zip(goal_vector.into_iter()) {
                    let start = sys.names.get_or_insert_key(var);
                    assert_eq!(kleene_local(&sys, start, &$oracle), goal);
                }
            }
        };
    }
    #[test]
    fn test_kleene_local_smax_ff_tt() {
        let oracle = SMax::hash();
        let mut sys1 = bool_system! {
            x = tt;
        };
        let start1 = sys1.names.get_or_insert_key("x");
        assert!(kleene_local(&sys1, start1, &oracle));
        let mut sys2 = bool_system! {
            x = ff;
        };
        let start2 = sys2.names.get_or_insert_key("x");
        assert!(!kleene_local(&sys2, start2, &oracle));
    }

    macro_rules! test_oracles {
        ( $( $oracle:expr, $name:ident );*) => {
            $(
                test_oracle!($oracle, $name);
            )*
        };
    }

    #[test]
    fn test_kleene_local_smax_and() {
        let oracle = SMax::hash();
        let mut sys1 = bool_system! {
            x = (y && z);
            y = tt;
            z = tt;
        };
        let start1 = sys1.names.get_or_insert_key("x");
        assert!(kleene_local(&sys1, start1, &oracle));

        let mut sys2 = bool_system! {
            x =(y && z);
            y = tt;
            z = ff;
        };
        let start2 = sys2.names.get_or_insert_key("x");
        assert!(!kleene_local(&sys2, start2, &oracle));
        let mut sys3 = bool_system! {
            x =(y && z);
            y = ff;
            z = ff;
        };
        let start3 = sys3.names.get_or_insert_key("x");
        assert!(!kleene_local(&sys3, start3, &oracle));
    }
    #[test]
    fn test_kleene_local_smax_or() {
        let oracle = SMax::hash();
        let mut sys1 = bool_system! {
            x =(y || z);
            y = tt;
            z = tt;
        };
        let start1 = sys1.names.get_or_insert_key("x");
        assert!(kleene_local(&sys1, start1, &oracle));
        let mut sys2 = bool_system! {
            x =(y || z);
            y = tt;
            z = ff;
        };
        let start2 = sys2.names.get_or_insert_key("x");
        assert!(kleene_local(&sys2, start2, &oracle));
        let mut sys3 = bool_system! {
            x =(y || z);
            y = ff;
            z = ff;
        };
        let start3 = sys3.names.get_or_insert_key("x");
        assert!(!kleene_local(&sys3, start3, &oracle));
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
        let oracle = SMax::hash();
        assert!(!kleene_local(&sys1, start1, &oracle));

        let mut sys2 = bool_system! {
            x = (((y || z) && k) || j);
            y = ff;
            z = ff;
            k = tt;
            j = tt;
        };
        let start2 = sys2.names.get_or_insert_key("x");
        assert!(kleene_local(&sys2, start2, &oracle));
        assert_ne!(
            kleene_local(&sys1, start1, &oracle),
            kleene_local(&sys2, start2, &oracle)
        );
    }

    test_oracles!(
        SMax::hash(),
        test_kleene_local_smax;
        TrivialOracle,
        test_kleene_local_trivialoracle;
        LocalMaxR::hash(),
        test_kleene_local_localmaxr;
        TrivialOracle.and(SMax::hash()),
        test_kleene_local_trivialoracle_and_smax;
        LocalMaxR::hash().and(SMax::hash()),
        test_kleene_local_localmaxr_and_smax;
        LocalMaxR::hash().and(TrivialOracle),
        test_kleene_local_localmaxr_and_trivialoracle;
        TrivialOracle.then(SMax::hash()),
        test_kleene_local_trivialoracle_then_smax;
        TrivialOracle.then(LocalMaxR::hash()),
        test_kleene_local_trivialoracle_then_localmaxr;
        SMax::hash().then(TrivialOracle),
        test_kleene_local_smax_then_trivialoracle;
        SMax::hash().then(LocalMaxR::hash()),
        test_kleene_local_smax_then_localmaxr;
        LocalMaxR::hash().then(SMax::hash()),
        test_kleene_local_localmaxr_then_smax;
        LocalMaxR::hash().then(TrivialOracle),
        test_kleene_local_localmaxr_then_trivialoracle
    );
}
