;;category calling-convention
;;exitcode 17
define i64 @foo(i64 %x) {
  ret i64 %x
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @foo(i64 17)
  ret i64 %1
}

