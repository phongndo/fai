// An HFIR module: the layer frontends write. Without a `layer` line a module is HFIR, so
// `layer hfir` prints as nothing. HFIR addresses struct fields and array elements by type.
// run: @point(3, 4) -> returned i32 25
// run: @second(7) -> returned i32 7
layer hfir

func @point(%x: i32, %y: i32) -> i32 {
  %p: ptr = mem.stack.of struct<C>{i8, i32}, align 1
  %fx: ptr = ptr.field.inbounds struct<C>{i8, i32} %p, 1
  mem.store i32 %x, %fx, align 4
  %a: i32 = mem.load %fx, align 4
  %a2: i32 = int.mul.nsw %a, %a
  %b2: i32 = int.mul.nsw %y, %y
  %r: i32 = int.add.nsw %a2, %b2
  func.ret %r
}

func @second(%v: i32) -> i32 {
  %arr: ptr = mem.stack.of array<4 x i32>, align 1
  %one: i64 = int.const 1
  %e: ptr = ptr.index.inbounds i32 %arr, %one
  mem.store i32 %v, %e, align 4
  %w: i32 = mem.load %e, align 4
  func.ret %w
}
