// The HFIR module of hfir.fir in MFIR, where `ptr.field` and `ptr.index` are not allowed:
// field and element addresses are `ptr.offset` by offsets computed from the data layout,
// here with `ty.offset` and the element stride. The interpreter runs both layers alike.
// run: @point(3, 4) -> returned i32 25
// run: @second(7) -> returned i32 7
// An out-of-bounds field offset is poison, as `ptr.field.inbounds` would give.
// run: @oob() -> returned ptr poison
layer mfir
memspace default ptr 32 addr 32

func @point(%x: i32, %y: i32) -> i32 {
  %p: ptr = mem.stack.of struct<C>{i8, i32}, align 1
  %o: i32 = ty.offset struct<C>{i8, i32}, 1
  %fx: ptr = ptr.offset.inbounds %p, %o
  mem.store i32 %x, %fx, align 4
  %a: i32 = mem.load %fx, align 4
  %a2: i32 = int.mul.nsw %a, %a
  %b2: i32 = int.mul.nsw %y, %y
  %r: i32 = int.add.nsw %a2, %b2
  func.ret %r
}

func @second(%v: i32) -> i32 {
  %arr: ptr = mem.stack.of array<4 x i32>, align 1
  %one: i32 = int.const 1
  %stride: i32 = int.const 4
  %off: i32 = int.mul.nsw %one, %stride
  %e: ptr = ptr.offset.inbounds %arr, %off
  mem.store i32 %v, %e, align 4
  %w: i32 = "mem.load"(%e) {align = 4}
  func.ret %w
}

func @oob() -> ptr {
  %p: ptr = mem.stack 4, align 4
  %o: i32 = ty.offset struct<C>{i32, i32}, 1
  %f: ptr = ptr.offset.inbounds %p, %o
  %g: ptr = ptr.offset.inbounds %f, %o
  func.ret %g
}
