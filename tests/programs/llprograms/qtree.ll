;;category uncategorized
;;exitcode 3
%vec = type [2 x i64]
%centroid = type { i64, [2 x i64] }
%qtree = type { %centroid, [4 x %qtree*] }
%qtrees = type [1 x %qtree]

@gbl = global %qtrees [ %qtree { %centroid { i64 1, [2 x i64] [ i64 2, i64 3 ] }, [4 x %qtree*] [ %qtree* null, %qtree* null, %qtree* null, %qtree* null ] } ]

define i64 @main(i64 %argc, i8** %argv) {
  %1 = getelementptr %qtrees, %qtrees* @gbl, i32 0, i32 0, i32 0, i32 1, i32 1
  %2 = load i64, i64* %1
  ret i64 %2
}

