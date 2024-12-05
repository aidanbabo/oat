use proptest::prelude::*;
use internment::Arena;

proptest! {
    #[test]
    fn doesnt_crash(s in "\\PC*") {
        let arena = Arena::new();
        let _ = oat::llvm::parse(&s, &arena);
    }
}
