// Aggregate values (decision: Aggregate values): structs and arrays as SSA values, built and
// taken apart with agg.make, agg.extract, and agg.insert, passed through regions and calls, and
// loaded and stored leaf by leaf with padding untouched. HFIR lowers them to their scalars.

func @pair(%a: i32, %p: ptr) -> i32 {
  %s: struct<C>{i32, ptr} = agg.make %a, %p @2:3
  %t: struct<C>{i32, ptr} = agg.insert %s, %a, 0 @3:3
  %x: i32 = agg.extract %t, 0 @4:3
  %q: ptr = agg.extract %t, 1 @5:3
  %c: i1 = ptr.cmp.eq %q, %p @6:3
  %z: i32 = int.zext %c @7:3
  %r: i32 = int.add.wrap %x, %z @8:3
  func.ret %r @9:3
}

// Nested: a struct holding an array and a struct.
func @nested(%a: i8, %b: i8) -> i8 {
  %arr: array<2 x i8> = agg.make %a, %b @12:3
  %w: i64 = int.sext %a @13:3
  %in: struct<packed>{i8, i64} = agg.make %b, %w @13:3
  %h: i16 = int.zext %b @14:3
  %o: struct<auto>{array<2 x i8>, i16, i8} = agg.make %arr, %h, %a @14:3
  %arr2: array<2 x i8> = agg.extract %o, 0 @15:3
  %y: i8 = agg.extract %arr2, 1 @16:3
  %o2: struct<auto>{array<2 x i8>, i16, i8} = agg.insert %o, %arr, 0 @17:3
  %x: i8 = agg.extract %o2, 2 @18:3
  %r: i8 = int.add.wrap %x, %y @19:3
  func.ret %r @20:3
}

// Through cf.if results, loop state, and block arguments.
func @flow(%n: i32) -> i32 {
  %zero: i32 = int.const 0 @23:3
  %one: i32 = int.const 1 @24:3
  %s0: struct<C>{i32, i32} = agg.make %zero, %zero @25:3
  %s: struct<C>{i32, i32} = cf.loop iter(%acc: struct<C>{i32, i32} = %s0) {
    %i: i32 = agg.extract %acc, 0 @27:5
    %sum: i32 = agg.extract %acc, 1 @28:5
    %done: i1 = int.cmp.sge %i, %n @29:5
    cf.if %done {
      cf.break %acc @31:7
    } else {
      cf.yield @33:7
    }
    %i2: i32 = int.add.wrap %i, %one @35:5
    %sum2: i32 = int.add.wrap %sum, %i @36:5
    %next: struct<C>{i32, i32} = agg.make %i2, %sum2 @37:5
    cf.continue %next @38:5
  }
  %b: struct<C>{i32, i32} = cf.blocks {
  ^entry:
    cf.br ^swap(%s) @42:5
  ^swap(%v: struct<C>{i32, i32}):
    %p: i32 = agg.extract %v, 0 @44:5
    %q: i32 = agg.extract %v, 1 @45:5
    %w: struct<C>{i32, i32} = agg.make %q, %p @46:5
    cf.yield %w @47:5
  }
  %r: i32 = agg.extract %b, 0 @49:3
  func.ret %r @50:3
}

// Through calls: an aggregate parameter and result, and an indirect call.
func @swap(%v: struct<C>{i8, i32}) -> struct<C>{i32, i8} {
  %a: i8 = agg.extract %v, 0 @54:3
  %b: i32 = agg.extract %v, 1 @55:3
  %w: struct<C>{i32, i8} = agg.make %b, %a @56:3
  func.ret %w @57:3
}

func @call(%a: i8, %b: i32) -> struct<C>{i32, i8} {
  %v: struct<C>{i8, i32} = agg.make %a, %b @61:3
  %w: struct<C>{i32, i8} = func.call @swap(%v) @62:3
  %f: ptr = func.addr @swap @63:3
  %x: struct<C>{i32, i8} = func.call.indirect func<(struct<C>{i8, i32}) -> struct<C>{i32, i8}> %f(%v) @64:3
  %eq: i32 = agg.extract %x, 0 @65:3
  func.ret %w @66:3
}

// Memory: a store writes the leaves only, so padding keeps its bytes; a load reads the leaves.
func @padding() -> (struct<C>{i8, i32}, b64) {
  %p: ptr = mem.stack.of struct<C>{i8, i32}, align 8 @70:3
  %ff: i64 = int.const -1 @71:3
  mem.store i64 %ff, %p, align 8 @72:3
  %a: i8 = int.const 1 @73:3
  %b: i32 = int.const 2 @74:3
  %s: struct<C>{i8, i32} = agg.make %a, %b @75:3
  mem.store struct<C>{i8, i32} %s, %p, align 4 @76:3
  %t: struct<C>{i8, i32} = mem.load %p, align 4 @77:3
  %raw: b64 = mem.load %p, align 8 @78:3
  func.ret %t, %raw @79:3
}

// A load of an uninitialized struct gives poison leaves; a leaf out of bounds is UB at that leaf.
func @fresh() -> array<2 x i16> {
  %p: ptr = mem.stack 4, align 2 @83:3
  %v: array<2 x i16> = mem.load %p, align 2 @84:3
  func.ret %v @85:3
}

func @short() -> struct<C>{i32, i32} {
  %p: ptr = mem.stack 6, align 4 @89:3
  %v: struct<C>{i32, i32} = mem.load %p, align 4 @90:3
  func.ret %v @91:3
}

func @holes(%a: i8) -> i8 {
  %s: struct<C>{i8, i64} = agg.make %a, ?h: i64 @97:3
  %x: i8 = agg.extract %s, 0 @98:3
  func.ret %x @99:3
}

// run: @pair(5, null) -> returned i32 6
// run: @nested(3, 4) -> returned i8 7
// run: @flow(5) -> returned i32 10
// run: @flow(0) -> returned i32 0
// run: @call(7, 9) -> returned {i32 9, i8 7}
// run: @padding() -> returned {i8 1, i32 2}, b64 (0x1, 0xff, 0xff, 0xff, 0x2, 0x0, 0x0, 0x0)
// A hole in an aggregate is reached when the aggregate is built.
// run: @holes(1) -> hole ?h @97:3
// run: @fresh() -> returned {i16 poison, i16 poison}
// run: @short() -> ub out-of-bounds @90:3 (offset 4, 4 bytes, allocation size 6)
