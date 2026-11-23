// Functions that take a struct, a nested struct, a union, and a slice, and that nothing in the
// module calls. A `// run:` line can only give scalars, so none of them can be run from here,
// and without a caller no run reaches them through another function either: the lowering test
// runs each on generated values, and its lowering on the same values as the lowered signature
// takes them (`fir::interp::run_lowering_pair`). Each result depends on which part is which.
// run: @marker(7) -> returned i32 7

func @marker(%x: i32) -> i32 {
  func.ret %x
}

func @fields(%p: struct<C>{i32, i32}) -> i32 {
  %a: i32 = agg.extract %p, 0
  %b: i32 = agg.extract %p, 1
  %twice: i32 = int.add.wrap %a, %a
  %r: i32 = int.sub.wrap %twice, %b
  func.ret %r
}

func @nested(%o: struct<C>{array<2 x i8>, i8, i8}) -> i8 {
  %arr: array<2 x i8> = agg.extract %o, 0
  %first: i8 = agg.extract %arr, 0
  %second: i8 = agg.extract %arr, 1
  %last: i8 = agg.extract %o, 2
  %d: i8 = int.sub.wrap %first, %second
  %r: i8 = int.sub.wrap %d, %last
  func.ret %r
}

func @variant(%u: union<i64, i32>) -> i32 {
  %t: i32 = union.tag %u
  %v: i32 = union.get.trap %u, 1
  %r: i32 = int.sub.wrap %v, %t
  func.ret %r
}

func @length(%s: slice) -> i64 {
  %n: i64 = slice.len %s
  func.ret %n
}
