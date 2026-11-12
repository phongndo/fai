// Float initializers: a float global reads its literal in its own format, integers and the
// special values included, and so does a float field or element of a list initializer.
global @a: f64 = 1.5
global const @b: f32 = -0.0
global @c: struct<C>{i8, f32, f64} = {7, 0.1, -inf}
global @d: array<3 x f32> = {1, nan(0x1), 3.4028234663852886e38}
global const @e: f64 = -nan(0x3)
global @f: f64 = 4.9e-324

// run: @scalars() -> returned f64 1.5, f32 -0.0, f64 -nan(0x3), f64 5e-324
// run: @fields() -> returned i8 7, f32 0.1, f64 -inf
// run: @elems() -> returned f32 1.0, f32 nan(0x1), f32 3.4028235e38
// run: @bits() -> returned i32 1036831949, i64 -4503599627370493
// run: @bump(2.0) -> returned f64 3.5, f64 3.5
func @scalars() -> (f64, f32, f64, f64) {
  %pa: ptr = mem.global @a
  %a: f64 = mem.load %pa, align 8
  %pb: ptr = mem.global @b
  %b: f32 = mem.load %pb, align 4
  %pe: ptr = mem.global @e
  %e: f64 = mem.load %pe, align 8
  %pf: ptr = mem.global @f
  %f: f64 = mem.load %pf, align 8
  func.ret %a, %b, %e, %f
}

func @fields() -> (i8, f32, f64) {
  %p: ptr = mem.global @c
  %q: ptr = ptr.field.inbounds struct<C>{i8, f32, f64} %p, 1
  %r: ptr = ptr.field.inbounds struct<C>{i8, f32, f64} %p, 2
  %x: i8 = mem.load %p, align 1
  %y: f32 = mem.load %q, align 4
  %z: f64 = mem.load %r, align 8
  func.ret %x, %y, %z
}

func @elems() -> (f32, f32, f32) {
  %p: ptr = mem.global @d
  %four: i64 = int.const 4
  %eight: i64 = int.const 8
  %q: ptr = ptr.offset.inbounds %p, %four
  %r: ptr = ptr.offset.inbounds %p, %eight
  %x: f32 = mem.load %p, align 4
  %y: f32 = mem.load %q, align 4
  %z: f32 = mem.load %r, align 4
  func.ret %x, %y, %z
}

// The initializers' bits in memory.
func @bits() -> (i32, i64) {
  %p: ptr = mem.global @c
  %four: i64 = int.const 4
  %q: ptr = ptr.offset.inbounds %p, %four
  %x: i32 = mem.load %q, align 4
  %pe: ptr = mem.global @e
  %y: i64 = mem.load %pe, align 8
  func.ret %x, %y
}

func @bump(%x: f64) -> (f64, f64) {
  %p: ptr = mem.global @a
  %a: f64 = mem.load %p, align 8
  %s: f64 = float.add %a, %x
  mem.store f64 %s, %p, align 8
  %t: f64 = mem.load %p, align 8
  func.ret %s, %t
}
