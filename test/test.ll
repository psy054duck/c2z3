; ModuleID = 'test/test.c'
source_filename = "test/test.c"
target datalayout = "e-m:o-i64:64-i128:128-n32:64-S128"
target triple = "arm64-apple-macosx13.0.0"

; Function Attrs: noinline nounwind ssp uwtable
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  store i32 0, ptr %2, align 4
  store i32 0, ptr %3, align 4
  store i32 5000000, ptr %4, align 4
  br label %5

5:                                                ; preds = %9, %0
  %6 = load i32, ptr %2, align 4
  %7 = load i32, ptr %4, align 4
  %8 = icmp ult i32 %6, %7
  br i1 %8, label %9, label %14

9:                                                ; preds = %5
  %10 = load i32, ptr %2, align 4
  %11 = add i32 %10, 2
  store i32 %11, ptr %2, align 4
  %12 = load i32, ptr %3, align 4
  %13 = add i32 %12, 4
  store i32 %13, ptr %3, align 4
  br label %5, !llvm.loop !5

14:                                               ; preds = %5
  %15 = load i32, ptr %3, align 4
  %16 = load i32, ptr %4, align 4
  %17 = mul i32 2, %16
  %18 = icmp eq i32 %15, %17
  call void @assert(i1 noundef zeroext %18)
  ret i32 0
}

declare void @assert(i1 noundef zeroext) #1

attributes #0 = { noinline nounwind ssp uwtable "frame-pointer"="non-leaf" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="apple-m1" "target-features"="+aes,+crc,+crypto,+dotprod,+fp-armv8,+fp16fml,+fullfp16,+lse,+neon,+ras,+rcpc,+rdm,+sha2,+sha3,+sm4,+v8.5a,+zcm,+zcz" }
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
