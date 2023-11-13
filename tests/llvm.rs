use oat::llvm;
use std::fs;

macro_rules! interp_test {
    ($binop:ident, $tests:ident) => {
        #[test]
        fn $binop() {
            for &(test, ret) in $tests {
                let s = fs::read_to_string(format!("tests/programs/{test}")).expect("failed to read file");
                let prog = llvm::parse(&s).expect(test);
                let r = llvm::interp::interp_prog(&prog, &[]).expect("execution failed");
                assert_eq!(r, ret, "failed on test {test}");
            }
        }
    };
}

interp_test!(binop_interp, BINOP_TESTS);
interp_test!(calling_converntion_interp, CALLING_CONVENTION_TESTS);
interp_test!(memory_interp, MEMORY_TESTS);
interp_test!(terminator_interp, TERMINATOR_TESTS);
interp_test!(bitcast_interp, BITCAST_TESTS);
interp_test!(gep_interp, GEP_TESTS);
// interp_test!(IO_TESTS);
interp_test!(large_interp, LARGE_TESTS);

const BINOP_TESTS: &[(&str, i64)] = &[
    ("llprograms/add.ll", 14),
    ("llprograms/sub.ll", 1),
    ("llprograms/mul.ll", 45),
    ("llprograms/and.ll", 0),
    ("llprograms/or.ll",  1),
    ("llprograms/xor.ll", 0),
    ("llprograms/shl.ll", 168),
    ("llprograms/lshr.ll", 10),
    ("llprograms/ashr.ll", 5),
];

const CALLING_CONVENTION_TESTS: &[(&str, i64)] = &[
    ("llprograms/call.ll", 42),
    ("llprograms/call1.ll", 17),
    ("llprograms/call2.ll", 19),
    ("llprograms/call3.ll", 34),
    ("llprograms/call4.ll", 34),
    ("llprograms/call5.ll", 24),
    ("llprograms/call6.ll", 26),
];

const MEMORY_TESTS: &[(&str, i64)] = &[
    ("llprograms/alloca1.ll", 17),
    ("llprograms/alloca2.ll", 17),
    ("llprograms/global1.ll", 12),
];

const TERMINATOR_TESTS: &[(&str, i64)] = &[
    ("llprograms/return.ll", 0),
    ("llprograms/return42.ll", 42),
    ("llprograms/br1.ll", 9),
    ("llprograms/br2.ll", 17),
    ("llprograms/cbr1.ll", 7),
    ("llprograms/cbr2.ll", 9),
    ("llprograms/duplicate_lbl.ll", 1),
];

const BITCAST_TESTS: &[(&str, i64)] = &[
    ("llprograms/bitcast1.ll", 3),
];

const GEP_TESTS: &[(&str, i64)] = &[
    ("llprograms/gep1.ll", 6),
    ("llprograms/gep2.ll", 4),
    ("llprograms/gep3.ll", 1),
    ("llprograms/gep4.ll", 2),
    ("llprograms/gep5.ll", 4),
    ("llprograms/gep6.ll", 7),
    // ("llprograms/gep7.ll", 7), OOB
    ("llprograms/gep8.ll", 2),
];

const IO_TESTS: &[(&str, &[&str], &str)] = &[
    ("llprograms/helloworld.ll", &[], "hello, world!"),
    ("llprograms/string1.ll", &[], "hello, world!hello, world!"),
    ("llprograms/callback1.ll", &[], "38"),
    ("llprograms/args1.ll", &["hello"], "argc < 3"),
    ("llprograms/args1.ll", &["hello", "cis341"], "hellocis341"),
    ("llprograms/args1.ll", &["hello", "cis341", "foo"], "argc > 3"),
];

const LARGE_TESTS: &[(&str, i64)] = &[
    ("llprograms/list1.ll", 3),
    ("llprograms/cbr.ll", 42),
    ("llprograms/factorial.ll", 120),
    ("llprograms/factrect.ll", 120),
    ("llprograms/duplicate_factorial.ll", 240),
];
