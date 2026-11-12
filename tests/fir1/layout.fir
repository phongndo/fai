// Struct and array layout in the default data layout (x86-64 System V).
// C layout: i8 at 0, ptr at 8, i16 at 16; size 24, alignment 8.
// run: @c() -> returned i64 24, i64 8, i64 0, i64 8, i64 16
// Packed: no padding, alignment 1.
// run: @packed() -> returned i64 11, i64 1, i64 1, i64 9
// Auto: by decreasing alignment, stably: ptr at 0, i32 at 8, the two i8s at 12 and 13.
// run: @auto() -> returned i64 16, i64 8, i64 12, i64 0, i64 8, i64 13
// Arrays: the elements' strides; nested structs and arrays; an empty struct.
// run: @arrays() -> returned i64 40, i64 4, i64 48, i64 8, i64 0, i64 1, i64 6
// i128 aligns to 16; i24 to 4 (the next listed width), with a 3-byte size and a 4-byte stride.
// run: @ints() -> returned i64 32, i64 16, i64 16, i64 4, i64 3, i64 8
func @c() -> (i64, i64, i64, i64, i64) {
  %s: i64 = ty.size struct<C>{i8, ptr, i16}
  %a: i64 = ty.align struct<C>{i8, ptr, i16}
  %o0: i64 = ty.offset struct<C>{i8, ptr, i16}, 0
  %o1: i64 = ty.offset struct<C>{i8, ptr, i16}, 1
  %o2: i64 = ty.offset struct<C>{i8, ptr, i16}, 2
  func.ret %s, %a, %o0, %o1, %o2
}

func @packed() -> (i64, i64, i64, i64) {
  %s: i64 = ty.size struct<packed>{i8, ptr, i16}
  %a: i64 = ty.align struct<packed>{i8, ptr, i16}
  %o1: i64 = ty.offset struct<packed>{i8, ptr, i16}, 1
  %o2: i64 = ty.offset struct<packed>{i8, ptr, i16}, 2
  func.ret %s, %a, %o1, %o2
}

func @auto() -> (i64, i64, i64, i64, i64, i64) {
  %s: i64 = ty.size struct<auto>{i8, ptr, i32, i8}
  %a: i64 = ty.align struct<auto>{i8, ptr, i32, i8}
  %o0: i64 = ty.offset struct<auto>{i8, ptr, i32, i8}, 0
  %o1: i64 = ty.offset struct<auto>{i8, ptr, i32, i8}, 1
  %o2: i64 = ty.offset struct<auto>{i8, ptr, i32, i8}, 2
  %o3: i64 = ty.offset struct<auto>{i8, ptr, i32, i8}, 3
  func.ret %s, %a, %o0, %o1, %o2, %o3
}

func @arrays() -> (i64, i64, i64, i64, i64, i64, i64) {
  %s: i64 = ty.size array<10 x i32>
  %a: i64 = ty.align array<10 x i32>
  %n: i64 = ty.size array<2 x struct<C>{i8, ptr, i16}>
  %o: i64 = ty.offset struct<C>{i32, array<3 x b8>, ptr}, 2
  %e: i64 = ty.size struct<C>{}
  %ea: i64 = ty.align struct<C>{}
  %p: i64 = ty.size array<3 x struct<packed>{i8, i8}>
  func.ret %s, %a, %n, %o, %e, %ea, %p
}

func @ints() -> (i64, i64, i64, i64, i64, i64) {
  %s: i64 = ty.size struct<C>{i8, i128}
  %a: i64 = ty.align i128
  %o: i64 = ty.offset struct<C>{i8, i128}, 1
  %a24: i64 = ty.align i24
  %s24: i64 = ty.size i24
  %n24: i64 = ty.size array<2 x i24>
  func.ret %s, %a, %o, %a24, %s24, %n24
}
