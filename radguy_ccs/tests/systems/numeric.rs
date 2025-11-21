use radguy_ccs::{
    numeric_system,
    systems::numeric::{Number, numeric_system::NumericSystemImpl},
};
use slotmap::DefaultKey;

pub struct NumericSystemSpec {
    pub system: NumericSystemImpl<DefaultKey, DefaultKey, &'static str>,
    pub variables: Vec<&'static str>,
    pub goal: Vec<Number>,
}

macro_rules! convert_number {
    (inf) => {
        Number::Inf
    };
    ($val:literal) => {
        Number::Val($val)
    };
}

/// Generate a [`SystemSpec`] from a definition of a boolean system
/// The format for the spec of a variable is:
/// ```
/// <expected value> => <name> = <definition>;
/// ```
macro_rules! numeric_system_spec {
    ($($name:ident: {
        $($val:tt => $varname:ident = $def:tt;)*
    };)*) => {
        $(
            #[must_use]
            pub fn $name() -> NumericSystemSpec {
                let system = numeric_system! {
                    $($varname = $def;)*
                };
                let variables = vec![$(stringify!($varname),)*];
                let goal = vec![$(convert_number!{$val},)*];
                NumericSystemSpec {
                    system,
                    variables,
                    goal,
                }
            }
        )*
    };
}

numeric_system_spec! {
    large: {
        10 => x = (min((min(y, z)), j));
        100 => y = (k * i);
        10 => z = m;
        20 => k = (min(((i * i) + (1 * l)), (l * m)));
        20 => j = (z * l);
        5 => i = 5;
        2 => l = 2;
        10 => m = 10;
    };
    inf: {
        inf => x = inf;
    };
    literal: {
        5 => x = 5;
    };
    reference: {
        3 => x = y;
        3 => y = 3;
    };
    add_literal_literal: {
        8 => x = (5 + 3);
    };
    add_inf_literal: {
        inf => x = (inf + 3);
    };
    add_literal_inf: {
        inf => x = (5 + inf);
    };
    add_inf_inf: {
        inf => x = (inf + inf);
    };
    mult_literal_literal: {
        20 => x = (4 * 5);
    };
    mult_inf_literal: {
        inf => x = (inf * 5);
    };
    mult_literal_inf: {
        inf => x = (4 * inf);
    };
    mult_inf_inf: {
        inf => x = (inf * inf);
    };
    min_literal_literal: {
        12 => x = (min(12, 13));
    };
    min_inf_literal: {
        13 => x = (min(inf, 13));
    };
    min_literal_inf: {
        14 => x = (min(14, inf));
    };
    min_inf_inf: {
        inf => x = (min(inf, inf));
    };
    max_literal_literal: {
        13 => x = (max(12, 13));
    };
    max_inf_literal: {
        inf => x = (max(inf, 13));
    };
    max_literal_inf: {
        inf => x = (max(14, inf));
    };
    max_inf_inf: {
        inf => x = (max(inf, inf));
    };
    chain_literal: {
        321 => x = y;
        321 => y = z;
        321 => z = 321;
    };
    chain_infinity: {
        inf => x = y;
        inf => y = z;
        inf => z = inf;
    };
    recursive: {
        inf => x = (x + 1);
    };
    mutual_recursion: {
        inf => x = (y + 1);
        inf => y = (x + 1);
    };
}
