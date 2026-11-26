define dso_local void @store8(ptr %0, i64 %1, i8 %2) {
entry:
  %4 = getelementptr inbounds i8, ptr %0, i64 %1
  store i8 %2, ptr %4, align 1
  ret void
}
