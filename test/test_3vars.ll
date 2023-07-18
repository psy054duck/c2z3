; ModuleID = 'test/test.c'
source_filename = "test/test.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  %7 = call i32 @unknown1()
  store i32 %7, i32* %2, align 4
  %8 = call i32 @unknown2()
  store i32 %8, i32* %3, align 4
  %9 = load i32, i32* %2, align 4
  store i32 %9, i32* %4, align 4
  %10 = load i32, i32* %3, align 4
  store i32 %10, i32* %5, align 4
  store i32 0, i32* %6, align 4
  br label %11

11:                                               ; preds = %48, %0
  %12 = load i32, i32* %6, align 4
  %13 = icmp slt i32 %12, 10000
  br i1 %13, label %14, label %49

14:                                               ; preds = %11
  %15 = load i32, i32* %2, align 4
  %16 = icmp slt i32 %15, 5000
  br i1 %16, label %17, label %24

17:                                               ; preds = %14
  %18 = load i32, i32* %2, align 4
  %19 = add nsw i32 %18, 1
  store i32 %19, i32* %2, align 4
  %20 = load i32, i32* %3, align 4
  %21 = add nsw i32 %20, 2
  store i32 %21, i32* %3, align 4
  %22 = load i32, i32* %6, align 4
  %23 = add nsw i32 %22, 1
  store i32 %23, i32* %6, align 4
  br label %31

24:                                               ; preds = %14
  %25 = load i32, i32* %2, align 4
  %26 = add nsw i32 %25, 2
  store i32 %26, i32* %2, align 4
  %27 = load i32, i32* %3, align 4
  %28 = add nsw i32 %27, 1
  store i32 %28, i32* %3, align 4
  %29 = load i32, i32* %6, align 4
  %30 = add nsw i32 %29, 2
  store i32 %30, i32* %6, align 4
  br label %31

31:                                               ; preds = %24, %17
  %32 = load i32, i32* %3, align 4
  %33 = icmp sgt i32 %32, 500
  br i1 %33, label %34, label %41

34:                                               ; preds = %31
  %35 = load i32, i32* %3, align 4
  %36 = add nsw i32 %35, 3
  store i32 %36, i32* %3, align 4
  %37 = load i32, i32* %2, align 4
  %38 = add nsw i32 %37, 4
  store i32 %38, i32* %2, align 4
  %39 = load i32, i32* %6, align 4
  %40 = add nsw i32 %39, 3
  store i32 %40, i32* %6, align 4
  br label %48

41:                                               ; preds = %31
  %42 = load i32, i32* %2, align 4
  %43 = add nsw i32 %42, 6
  store i32 %43, i32* %2, align 4
  %44 = load i32, i32* %3, align 4
  %45 = add nsw i32 %44, 5
  store i32 %45, i32* %3, align 4
  %46 = load i32, i32* %6, align 4
  %47 = add nsw i32 %46, 4
  store i32 %47, i32* %6, align 4
  br label %48

48:                                               ; preds = %41, %34
  br label %11, !llvm.loop !6

49:                                               ; preds = %11
  %50 = load i32, i32* %6, align 4
  %51 = icmp sgt i32 %50, 0
  br i1 %51, label %52, label %60

52:                                               ; preds = %49
  %53 = load i32, i32* %2, align 4
  %54 = icmp eq i32 %53, 100
  br i1 %54, label %58, label %55

55:                                               ; preds = %52
  %56 = load i32, i32* %3, align 4
  %57 = icmp eq i32 %56, 10
  br label %58

58:                                               ; preds = %55, %52
  %59 = phi i1 [ true, %52 ], [ %57, %55 ]
  call void @assert(i1 noundef zeroext %59)
  br label %60

60:                                               ; preds = %58, %49
  %61 = load i32, i32* %2, align 4
  %62 = load i32, i32* %3, align 4
  %63 = add nsw i32 %61, %62
  ret i32 %63
}

declare i32 @unknown1() #1

declare i32 @unknown2() #1

declare void @assert(i1 noundef zeroext) #1

attributes #0 = { noinline nounwind optnone uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3, !4}
!llvm.ident = !{!5}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{i32 7, !"uwtable", i32 1}
!4 = !{i32 7, !"frame-pointer", i32 2}
!5 = !{!"Ubuntu clang version 14.0.0-1ubuntu1"}
!6 = distinct !{!6, !7}
!7 = !{!"llvm.loop.mustprogress"}
