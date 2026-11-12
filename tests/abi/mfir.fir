// MFIR passes structs and arrays whole across calls (decision: C ABI for aggregates), and makes
// and takes them apart with agg.make, agg.extract, and agg.insert.
layer mfir

func @bump(%s: struct<C>{i32, array<2 x f32>, ptr}, %k: i32) -> struct<C>{i32, array<2 x f32>, ptr} {
  %a: i32 = agg.extract %s, 0
  %b: i32 = int.add.wrap %a, %k
  %t: struct<C>{i32, array<2 x f32>, ptr} = agg.insert %s, %b, 0
  %arr: array<2 x f32> = agg.extract %t, 1
  %x: f32 = agg.extract %arr, 0
  %y: f32 = float.add %x, %x
  %arr2: array<2 x f32> = agg.insert %arr, %y, 1
  %u: struct<C>{i32, array<2 x f32>, ptr} = agg.insert %t, %arr2, 1
  %v: struct<C>{i32, array<2 x f32>, ptr} = copy %u
  func.ret %v
}

func @main(%k: i32) -> struct<C>{i32, array<2 x f32>, ptr} {
  %one: i32 = int.const 1
  %h: f32 = float.const 1.25
  %z: f32 = float.const 0.0
  %arr: array<2 x f32> = agg.make %h, %z
  %n: ptr = ptr.null
  %s: struct<C>{i32, array<2 x f32>, ptr} = agg.make %one, %arr, %n
  %r: struct<C>{i32, array<2 x f32>, ptr} = func.call @bump(%s, %k)
  %f: ptr = func.addr @bump
  %r2: struct<C>{i32, array<2 x f32>, ptr} = func.call.indirect func<(struct<C>{i32, array<2 x f32>, ptr}, i32) -> struct<C>{i32, array<2 x f32>, ptr}> %f(%r, %k)
  func.ret %r2
}

// run: @main(5) -> returned {i32 11, {f32 1.25, f32 2.5}, ptr null}
