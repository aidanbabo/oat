;;category terminator
;;exitcode 7
define i64 @main(i64 %argc, i8** %arcv) {
  %cmp = icmp sgt i64 3, 0
  br i1 %cmp, label %then, label %else
then:
  ret i64 7
else:
  ret i64 9
}

