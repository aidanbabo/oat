;;category binop
;;exitcode 168
define i64 @main(i64 %argc, i8** %arcv) {
  %1 = shl i64 42, 2
  ret i64 %1
}

