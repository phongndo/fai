// Sum of 0 .. n-1 with a `progress` loop and signed-overflow-is-poison adds.
// run: @sum(0) -> returned i32 0
// run: @sum(4) -> returned i32 6
// run: @sum(100) -> returned i32 4950
// The sum overflows i32, so the `.nsw` add gives poison, which flows to the result.
// run: @sum(70000) -> returned i32 poison
func @sum(%n: i32) -> i32 loc "sum.c" {
  %zero: i32 = int.const 0 @2:3
  %one: i32 = int.const 1 @2:3
  %r: i32 = cf.loop progress iter(%i: i32 = %zero, %acc: i32 = %zero) @3:3 {
    %done: i1 = int.cmp.sge %i, %n @3:17
    cf.if %done @3:17 {
      cf.break %acc @3:17
    }
    %acc2: i32 = int.add.nsw %acc, %i @4:9
    %i2: i32 = int.add.nsw %i, %one @3:24
    cf.continue %i2, %acc2 @3:3
  }
  func.ret %r @5:3
}
