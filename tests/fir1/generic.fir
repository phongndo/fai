// The generic form, `"name"(operands) {attributes} @loc (regions)`, for every op. It means what
// the readable form means, and prints in the readable form. Attributes come in any order.
// run: @ints(3, 7) -> returned i32 384
// run: @mem(9) -> returned i32 9
// run: @count(4) -> returned i32 4
// run: @calls(5) -> returned i32 5
func @ints(%a: i32, %b: i32) -> i32 {
  %c: i32 = "int.const"() {n = 5}
  %s: i32 = "int.add.nsw"(%a, %b)
  %d: i32 = "int.sub.wrap"(%s, %c) @3:5
  %m: i32 = "int.mul.s.trap"(%d, %b)
  %q: i32 = "int.div.s.trap.wrap"(%m, %b)
  %r: i32 = "int.rem.u.ub"(%q, %c)
  %x: i32 = "int.xor"(%r, %a)
  %sh: i32 = "int.shl.mask"(%x, %b)
  %lt: i1 = "int.cmp.slt"(%a, %b)
  %sel: i32 = "select"(%lt, %sh, %x)
  %w: i64 = "int.sext"(%sel)
  %u: i64 = "int.zext"(%a)
  %t: i32 = "int.trunc.wrap"(%w)
  %p: i32 = "poison"()
  %f: i32 = "freeze"(%p)
  %y: i32 = "copy"(%t)
  %res: i32 = "int.add.wrap"(%y, %f)
  "func.ret"(%res)
}

func @mem(%v: i32) -> i32 {
  %n: i64 = "int.const"() {n = 16}
  %h: ptr = "mem.alloc.null"(%n) {family = c.malloc, align = 8}
  %s: ptr = "mem.stack"() {size = 8, align = 4}
  "mem.store"(%v, %s) {align = 4, ty = i32}
  %x: i32 = "mem.load"(%s) {align = 4}
  %four: i64 = int.const 4
  %h4: ptr = "ptr.offset.inbounds"(%h, %four)
  "mem.store"(%x, %h4) {ty = i32, align = 4}
  %y: i32 = "mem.load"(%h4) {align = 4}
  %a: i64 = "ptr.addr"(%h)
  %e: i64 = "ptr.expose"(%h)
  %back: ptr = "ptr.from_exposed"(%e)
  %same: ptr = "ptr.with_addr"(%h, %a)
  %null: ptr = "ptr.null"()
  %ne: i1 = "ptr.cmp.ne"(%back, %null)
  "mem.free"(%same) {family = c.malloc}
  %r: i32 = "cf.if"(%ne) ({
    "cf.yield"(%y)
  }, {
    cf.yield %v
  })
  "func.ret"(%r)
}

func @count(%n: i32) -> i32 {
  %zero: i32 = int.const 0
  %r: i32 = "cf.loop"(%zero) {progress = true} @7:1 ((%i: i32 [range.s(0, 100) assume]) {
    %done: i1 = "int.cmp.sge"(%i, %n)
    "cf.if"(%done) ({
      "cf.break"(%i)
    }, {})
    %one: i32 = int.const 1
    %next: i32 = "int.add.nsw"(%i, %one)
    "cf.continue"(%next)
  })
  func.ret %r
}

func @calls(%n: i32) -> i32 {
  %r: i32 = "func.call"(%n) {callee = @count}
  "func.ret"(%r)
}
