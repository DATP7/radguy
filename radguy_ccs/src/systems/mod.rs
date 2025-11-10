pub mod bool;
pub mod ccs;
pub mod numeric;
pub mod wccs;
pub mod wctl;

#[cfg(test)]
pub(crate) mod test_utils {
    #[macro_export]
    macro_rules! assert_good {
        ($strs:expr, $parser:expr) => {
            let mut success = true;
            for s in $strs {
                let res = $parser.parse(s);
                match res {
                    Ok(_) => {}
                    Err(e) => {
                        dbg!(s);
                        dbg!("Expected Ok, but got error");
                        dbg!(e);
                        success = false;
                    }
                }
            }
            assert!(success);
        };
    }

    #[macro_export]
    macro_rules! assert_bad {
        ($strs:expr, $parser:expr) => {
            let mut success = true;
            for s in $strs {
                let res = $parser.parse(s);
                match res {
                    Ok(_) => {
                        dbg!(s);
                        dbg!("Expected error, but got Ok");
                        success = false;
                    }
                    Err(_) => {}
                }
            }
            assert!(success);
        };
    }
}
