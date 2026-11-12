// AAPCS64 classifies a composite as laid out (decision: C ABI for aggregates). A struct<auto>
// puts its f32 (align 4) before a packed struct of one f32 (align 1), so in declared order its
// leaves are at offsets 4 and 0. It is an HFA all the same, as C's
// `struct { float b; struct __attribute__((packed)) { float a; } p; }` is, and its members
// travel in memory order: s0 holds the field at offset 0 (the second declared), s1 the packed
// one. Subtraction tells the two apart.

extern func @peek(struct<auto>{struct<packed>{f32}, f32}) -> struct<auto>{struct<packed>{f32}, f32} effects[] assume

func @diff(%s: struct<auto>{struct<packed>{f32}, f32}) -> f32 {
  %p: struct<packed>{f32} = agg.extract %s, 0
  %a: f32 = agg.extract %p, 0
  %b: f32 = agg.extract %s, 1
  %r: f32 = float.sub %a, %b
  func.ret %r
}

// A result comes back in memory order too.
func @swap(%s: struct<auto>{struct<packed>{f32}, f32}) -> struct<auto>{struct<packed>{f32}, f32} {
  %p: struct<packed>{f32} = agg.extract %s, 0
  %a: f32 = agg.extract %p, 0
  %b: f32 = agg.extract %s, 1
  %q: struct<packed>{f32} = agg.make %b
  %r: struct<auto>{struct<packed>{f32}, f32} = agg.make %q, %a
  func.ret %r
}

func @order(%x: f32, %y: f32) -> (f32, f32) {
  %p: struct<packed>{f32} = agg.make %x
  %s: struct<auto>{struct<packed>{f32}, f32} = agg.make %p, %y
  %t: struct<auto>{struct<packed>{f32}, f32} = func.call @swap(%s)
  %d: f32 = func.call @diff(%s)
  %e: f32 = func.call @diff(%t)
  func.ret %d, %e
}

// To C and back: the event shows the value, fields as declared.
func @to_c(%x: f32, %y: f32) -> f32 {
  %p: struct<packed>{f32} = agg.make %x
  %s: struct<auto>{struct<packed>{f32}, f32} = agg.make %p, %y
  %t: struct<auto>{struct<packed>{f32}, f32} = func.call @peek(%s)
  %d: f32 = func.call @diff(%t)
  func.ret %d
}

// run: @order(2.5, 1.25) -> returned f32 1.25, f32 -1.25
// run: @to_c(2.5, 1.25) -> @peek({{f32 2.5}, f32 1.25}) -> {{f32 0.0}, f32 0.0}; returned f32 0.0
