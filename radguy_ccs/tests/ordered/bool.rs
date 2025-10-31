use super::systems;

macro_rules! test_oracle_systems {
    (test $oracle:expr, on: $($spec:ident),* $(,)?) => {
        $(
        #[test]
        fn $spec() {
            let $crate::systems::bool::SystemSpec {
                mut system,
                variables,
                goal,
            } = $crate::systems::bool::$spec();
            for (var, goal) in variables.into_iter().zip(goal.into_iter()) {
                let start = system.names.get_or_insert_key(var);
                assert_eq!(::radguy::kleene_local(&system, start, &$oracle), goal, "{var} did not have the expected value");
            }
        }
        )*
    };
}

macro_rules! test_oracle {
    ($oracle:expr, $name:ident) => {
        mod $name {
            use super::*;
            test_oracle_systems! {
                test $oracle, on:
                large,
                self_reference_true,
                self_reference_false,
                true_single,
                false_single,
                and_00,
                and_01,
                and_10,
                and_11,
                or_00,
                or_01,
                or_10,
                or_11,
                parens_true,
                parens_false,
            }
        }
    };
}
macro_rules! test_oracles {
        ( $( $oracle:expr, $name:ident; )*) => {
            $(
                test_oracle!($oracle, $name);
            )*
        };
    }
