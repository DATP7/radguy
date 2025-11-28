use radguy_ccs::{bool_system, systems::bool::BoolSystemImpl};

pub struct SystemSpec {
    pub system: BoolSystemImpl<usize, usize, &'static str>,
    pub variables: Vec<&'static str>,
    pub goal: Vec<bool>,
}

/// Generate a [`SystemSpec`] from a definition of a boolean system
/// The format for the spec of a variable is:
/// ```
/// <expected value> => <name> = <definition>;
/// ```
macro_rules! system_spec {
    ($($name:ident: {
        $($val:literal => $varname:ident = $def:tt;)*
    };)*) => {
        $(
            #[must_use]
            pub fn $name() -> SystemSpec {
                let system = bool_system! {
                    $($varname = $def;)*
                };
                let variables = vec![$(stringify!($varname),)*];
                let goal = vec![$($val,)*];
                SystemSpec {
                    system,
                    variables,
                    goal,
                }
            }
        )*
    };
}

system_spec! {
    large: {
        true  => x = (((y || z) && k) || j);
        true  => y = ((x || j) || (z && k));
        true  => z = ((a || b || (c && d)) || ((e || f) && g && h)) ;
        true  => k = tt;
        false => j = (j || j);
        false => a = j;
        false => b = a;
        true  => c = k;
        false => d = b;
        true  => e = c;
        false => f = d;
        true  => g = e;
        true  => h = g;
    };
    self_reference_true: {
        true => x = (x || tt);
    };
    self_reference_false: {
        false => x = x;
    };
    true_single: {
        true => x = tt;
    };
    false_single: {
        false => x = ff;
    };
    and_00: {
        false => x = (y && z);
        false => y = ff;
        false => z = ff;
    };
    and_01: {
        false => x = (y && z);
        true => y = tt;
        false => z = ff;
    };
    and_10: {
        false => x = (y && z);
        false => y = ff;
        true => z = tt;
    };
    and_11: {
        true => x = (y && z);
        true => y = tt;
        true => z = tt;
    };
    or_00: {
        false => x = (y || z);
        false => y = ff;
        false => z = ff;
    };
    or_01: {
        true => x = (y || z);
        true => y = tt;
        false => z = ff;
    };
    or_10: {
        true => x = (y || z);
        false => y = ff;
        true => z = tt;
    };
    or_11: {
        true => x = (y || z);
        true => y = tt;
        true => z = tt;
    };
    parens_true: {
        true => x = (((y || z) && k) || j);
        false => y = ff;
        false => z = ff;
        true => k = tt;
        true => j = tt;
    };
    parens_false: {
        false => x = ((y || z) && (k || j));
        false => y = ff;
        false => z = ff;
        true => k = tt;
        true => j = tt;
    };
    chain: {
        true => x = y;
        true => y = z;
        true => z = tt;
    };
}
