// Tagged unions (decision: Tagged unions): `union<T0, T1, …>` holds one variant and an `i32` tag
// saying which. Unions are SSA values only: they have no layout. Reading the wrong variant is UB
// with `.ub` and traps with reason `tag` with `.trap`. HFIR lowers a union to its tag and every
// variant's scalars, `poison` for the variants it doesn't hold.

func @tag(%x: i32) -> i32 {
  %u: union<i32, ptr, struct<C>{i8, i8}> = union.make %x, 0 @1:1
  %t: i32 = union.tag %u @2:1
  func.ret %t
}

func @get(%x: i32, %which: i1) -> i32 {
  %a: union<i64, i32> = union.make %x, 1 @3:1
  %p: ptr = ptr.null @4:1
  %b: union<i64, i32> = cf.if %which {
    %w: i64 = int.sext %x @5:1
    %c: union<i64, i32> = union.make %w, 0 @6:1
    cf.yield %c
  } else {
    cf.yield %a
  }
  %v: i32 = union.get.trap %b, 1 @7:1
  func.ret %v
}

func @get_ub(%x: i32, %which: i1) -> i32 {
  %a: union<i64, i32> = union.make %x, 1 @8:1
  %b: union<i64, i32> = cf.if %which {
    %w: i64 = int.sext %x @9:1
    %c: union<i64, i32> = union.make %w, 0 @10:1
    cf.yield %c
  } else {
    cf.yield %a
  }
  %v: i32 = union.get.ub %b, 1 @11:1
  func.ret %v
}

// A union of structs, and a union inside a union.
func @nested(%x: i8) -> i8 {
  %h: i16 = int.sext %x @12:1
  %s: struct<C>{i8, i16} = agg.make %x, %h @12:1
  %u: union<i8, struct<C>{i8, i16}> = union.make %s, 1 @13:1
  %v: union<union<i8, struct<C>{i8, i16}>, ptr> = union.make %u, 0 @14:1
  %u2: union<i8, struct<C>{i8, i16}> = union.get.trap %v, 0 @15:1
  %s2: struct<C>{i8, i16} = union.get.trap %u2, 1 @16:1
  %y: i8 = agg.extract %s2, 0 @17:1
  func.ret %y
}

// A union as a function's parameter and result, and returned from the outermost call.
func @wrap(%x: i8) -> union<i8, i16> {
  %u: union<i8, i16> = union.make %x, 0 @18:1
  func.ret %u
}

func @unwrap(%u: union<i8, i16>) -> i16 {
  %t: i32 = union.tag %u @19:1
  %z: i32 = int.const 0 @20:1
  %is8: i1 = int.cmp.eq %t, %z @21:1
  %r: i16 = cf.if %is8 {
    %b: i8 = union.get.ub %u, 0 @22:1
    %w: i16 = int.sext %b @23:1
    cf.yield %w
  } else {
    %w2: i16 = union.get.ub %u, 1 @24:1
    cf.yield %w2
  }
  func.ret %r
}

func @roundtrip(%x: i8) -> i16 {
  %u: union<i8, i16> = func.call @wrap(%x) @25:1
  %r: i16 = func.call @unwrap(%u) @26:1
  func.ret %r
}

// run: @tag(5) -> returned i32 0
// run: @get(7, 0) -> returned i32 7
// run: @get(7, 1) -> trap tag @7:1
// run: @get_ub(7, 0) -> returned i32 7
// run: @get_ub(7, 1) -> ub tag @11:1 (the union holds variant 0)
// run: @nested(3) -> returned i8 3
// run: @wrap(-3) -> returned {i32 0, i8 -3}
// run: @roundtrip(-3) -> returned i16 -3
