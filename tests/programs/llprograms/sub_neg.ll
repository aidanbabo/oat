;;category arith
;;exitcode 255
; 'Why, oh why, does the terminal only report the last byte?
define i64 @main(i64 %argc, i8** %arcv) {
  %1 = sub i64 9, 10
  ret i64 %1
}

