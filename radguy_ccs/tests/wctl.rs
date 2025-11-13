use radguy::kleene_local;
use radguy::oracle::SMax;
use radguy_ccs::systems::numeric::number::Number;
use radguy_ccs::systems::wccs;
use radguy_ccs::systems::wccs::wccs_system::WCCSSystem;
use radguy_ccs::systems::wctl;
use radguy_ccs::systems::wctl::system::WCTLSystem;
use slotmap::DefaultKey;

// macro_rules! wctl_test {
//     ($($process_name:literal, $formula_name:literal => $eq:literal in $wccs:expr, $wctl:expr;)*) => {
//         $(
//             {
//                 let wccs_parser = wccs::ProgramParser::new();
//                 let wccs_ast = wccs_parser
//                     .parse(&$wccs)
//                     .expect("Failed to parse WCCS program content.");
//                 let mut wccs_system = WCCSSystem::<DefaultKey>::default();
//                 wccs_system.insert_ast_bindings(wccs_ast);

//                 let wctl_parser = wctl::ProgramParser::new();
//                 let wctl_bindings = wctl_parser.parse(&$wctl).expect("Failed to parse WCTL program content.");
//                 let formula = wctl_bindings.get($formula_name).expect("Formula should be bound");

//                 let sys = WCTLSystem::<DefaultKey, DefaultKey, DefaultKey, DefaultKey, DefaultKey>::new(wccs_system);
//                 let process_key = sys.lookup_process($process_name).expect("Process name should be bound");
//                 let formula_key = sys.insert_ast_formula(formula.clone());
//                 let start = sys.get_var(*process_key, formula_key);

//                 let result = kleene_local(&sys, start, &SMax::default()) == Number::Val(0);
//                 assert_eq!($eq, result, "{} should{} satisfy {} in {} {}", $process_name, if !$eq { " not" } else {""}, $formula_name, $wccs, $wctl);
//             }
//         )*
//     };
// }

macro_rules! wctl_test {
    ($($test_name:tt: $($process_name:literal, $formula_str:expr => $eq:literal),* $(,)? in $wccs:expr;)*) => {
        $(
            #[test]
            fn $test_name()
            {
                $(
                    let wccs_parser = wccs::ProgramParser::new();
                    let wccs_ast = wccs_parser
                        .parse(&$wccs)
                        .expect("Failed to parse WCCS program content.");
                    let mut wccs_system = WCCSSystem::<DefaultKey>::default();
                    wccs_system.insert_ast_bindings(wccs_ast);

                    let formula_parser = wctl::grammar::FormulaParser::new();
                    let formula = formula_parser.parse($formula_str).expect("Formula should parse");

                    let sys = WCTLSystem::<DefaultKey, DefaultKey, DefaultKey, DefaultKey, DefaultKey>::new(wccs_system);
                    let process_key = sys.lookup_process($process_name).expect("Process name should be bound");
                    let formula_key = sys.insert_ast_formula(formula.clone());
                    let start = sys.get_var(*process_key, formula_key);

                    let result = kleene_local(&sys, start, &SMax::default()) == Number::Val(0);
                    assert_eq!($eq, result, "{} should{} satisfy {} in {}", $process_name, if !$eq { " not" } else {""}, $formula_str, $wccs);
                )*
            }
        )*
    };
}

wctl_test! {
    mower_example:
        "S0", "A mow U[<=6] dump" => true,
        "S0", "A mow U[<=4] dump" => false,
        in r"
        S0 := mow:(<go,2>.S1 + <go,2>.S2 + <go,2>.S3);
        S1 := mow:<go,1>.S4;
        S2 := mow:<go,2>.S4;
        S3 := mow:<go,1>.S5;
        S4 := mow:(<go,0>.S5 + <go,1>.S6);
        S5 := mow:<go,2>.S6;
        S6 := dump:<go,0>.S6;
    ";
    proposition: "S", "mow" => true in "S := mow:0;";
    proposition_multiple: "S", "mow && dump" => true in "S := mow:dump:0;";
    proposition_multiple_neg: "S", "mow && dump && dud" => false in "S := mow:dump:0;";
    linear_universal_final: "S", "AF dump" => true in "S := <go>.<go>.<go>.<go>.dump:0;";
    recursive: "S", "AF dump" => true in "S := <go>.dump:S;";
    recursive_neg: "S", "AF mow" => false in "S := <go>.dump:S;";
    compare: "S", "mow == 4" => true in "S := mow:0 + mow:0 + mow:0 + mow:0;";
    bit_protocol: "System", "EF[<= 35] delivered == 7" => true in include_str!("../systems/wccs/BitProtocol(B5M7).wccs");
}
