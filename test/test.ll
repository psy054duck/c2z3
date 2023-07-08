; ModuleID = 'test/test.c'
source_filename = "test/test.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx12.0.0"

; Function Attrs: noinline nounwind optnone ssp uwtable
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %7 = call i32 @unknown1()
  store i32 %7, ptr %2, align 4
  %8 = call i32 @unknown2()
  store i32 %8, ptr %3, align 4
  %9 = load i32, ptr %2, align 4
  store i32 %9, ptr %4, align 4
  %10 = load i32, ptr %3, align 4
  store i32 %10, ptr %5, align 4
  store i32 0, ptr %6, align 4
  br label %11

11:                                               ; preds = %19, %0
  %12 = load i32, ptr %6, align 4
  %13 = icmp slt i32 %12, 1
  br i1 %13, label %14, label %22

14:                                               ; preds = %11
  %15 = load i32, ptr %2, align 4
  %16 = add nsw i32 %15, 1
  store i32 %16, ptr %2, align 4
  %17 = load i32, ptr %3, align 4
  %18 = add nsw i32 %17, 2
  store i32 %18, ptr %3, align 4
  br label %19

19:                                               ; preds = %14
  %20 = load i32, ptr %6, align 4
  %21 = add nsw i32 %20, 1
  store i32 %21, ptr %6, align 4
  br label %11, !llvm.loop !5

22:                                               ; preds = %11
  %23 = load i32, ptr %3, align 4
  %24 = load i32, ptr %2, align 4
  %25 = add nsw i32 %23, %24
  %26 = load i32, ptr %4, align 4
  %27 = load i32, ptr %5, align 4
  %28 = add nsw i32 %26, %27
  %29 = add nsw i32 %28, 3
  %30 = icmp eq i32 %25, %29
  call void @assert(i1 noundef zeroext %30)
  %31 = load i32, ptr %2, align 4
  %32 = load i32, ptr %3, align 4
  %33 = add nsw i32 %31, %32
  ret i32 %33
}

declare i32 @unknown1() #1

declare i32 @unknown2() #1

declare void @assert(i1 noundef zeroext) #1

attributes #0 = { noinline nounwind optnone ssp uwtable "frame-pointer"="non-leaf" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+sha3,+sm4,+v8.5a,+zcm,+zcz" }
attributes #1 = { "frame-pointer"="non-leaf" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+sha3,+sm4,+v8.5a,+zcm,+zcz" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{i32 7, !"frame-pointer", i32 1}
!4 = !{!"Homebrew clang version 15.0.6"}
!5 = distinct !{!5, !6}
!6 = !{!"llvm.loop.mustprogress"}
