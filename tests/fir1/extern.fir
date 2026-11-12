// External functions: declared outside the module, with trust-tagged effects. A call to one is an
// event, listed before the outcome; `fir-ref run` answers every call with zeros and changes
// nothing.
// run: @hello() -> @puts(ptr #1) -> i32 0; returned i32 0
// A call that returns nothing, and one that returns two values.
// run: @seed(7) -> @srand(i32 7) -> (); returned
// run: @two() -> @divmod(i64 17, i64 5) -> i64 0, i64 0; returned i64 0
// Arguments are passed as they are, poison included.
// run: @seed(poison) -> @srand(i32 poison) -> (); returned
// Events stay in order, and UB or a trap after them doesn't take them back.
// run: @after_ub(1) -> @srand(i32 1) -> (); @srand(i32 2) -> (); ub div0 @4:3
// run: @after_trap(1) -> @srand(i32 1) -> (); trap div0 @3:3
// Facts on results constrain what the world returns: a violated one is UB, after the event.
// run: @need_env() -> @getenv(ptr #1) -> ptr null; ub fact @2:3 (%v breaks a fact)
// External functions have function pointers too, and calls through them are events.
// run: @indirect() -> @puts(ptr #1) -> i32 0; returned i32 0
// run: @from_table() -> @srand(i32 3) -> (); returned
// run: @wrong_sig() -> ub bad-call @2:3 (@puts has type func<(ptr) -> i32>)
// A loop of calls: one event per call.
// run: @loop(3) -> @srand(i32 0) -> (); @srand(i32 1) -> (); @srand(i32 2) -> (); returned
// Results are zero of every type; a dangling or poison pointer argument passes as it is.
// run: @zeros() -> @wide() -> i128 0, b32 (0x0, 0x0, 0x0, 0x0), ptr null; returned
// run: @dangling() -> @free_like(ptr #4) -> (); returned
// run: @poison_ptr(poison) -> @free_like(ptr poison) -> (); returned
global const @msg: array<6 x i8> = bytes "68656c6c6f00"
global const @table: array<1 x ptr> = {@srand}

extern func @puts(ptr) -> i32 effects[read(args)] assume
extern func @srand(i32) effects[] assume
extern func @divmod(i64, i64) -> (i64, i64) effects[] check
extern func @getenv(ptr) -> ptr effects[read(args), read(exposed), trap] assume
extern func @wide() -> (i128, b32, ptr) effects[alloc] assume
extern func @free_like(ptr) effects[write(args), free] assume

func @hello() -> i32 {
  %p: ptr = mem.global @msg
  %r: i32 = func.call @puts(%p)
  func.ret %r
}

func @seed(%x: i32) {
  func.call @srand(%x)
  func.ret
}

func @two() -> i64 {
  %a: i64 = int.const 17
  %b: i64 = int.const 5
  %q: i64, %r: i64 = func.call @divmod(%a, %b)
  func.ret %q
}

func @after_ub(%x: i32) -> i32 {
  func.call @srand(%x) @1:3
  %two: i32 = int.const 2 @2:3
  func.call @srand(%two) @3:3
  %z: i32 = int.const 0
  %d: i32 = int.div.s.ub %x, %z @4:3
  func.ret %d
}

func @after_trap(%x: i32) -> i32 {
  func.call @srand(%x) @1:3
  %z: i32 = int.const 0 @2:3
  %d: i32 = int.div.s.trap %x, %z @3:3
  func.ret %d
}

func @need_env() -> ptr {
  %k: ptr = mem.global @msg @1:3
  %v: ptr [nonnull assume] = func.call @getenv(%k) @2:3
  func.ret %v
}

func @indirect() -> i32 {
  %f: ptr = func.addr @puts
  %p: ptr = mem.global @msg
  %r: i32 = func.call.indirect func<(ptr) -> i32> %f(%p)
  func.ret %r
}

func @from_table() {
  %t: ptr = mem.global @table
  %f: ptr = mem.load %t, align 8
  %x: i32 = int.const 3
  func.call.indirect func<(i32)> %f(%x)
  func.ret
}

func @wrong_sig() -> i64 {
  %f: ptr = func.addr @puts @1:3
  %r: i64 = func.call.indirect func<() -> i64> %f() @2:3
  func.ret %r
}

func @loop(%n: i32) {
  %zero: i32 = int.const 0
  %one: i32 = int.const 1
  cf.loop iter(%i: i32 = %zero) {
    %done: i1 = int.cmp.sge %i, %n
    cf.if %done {
      cf.break
    }
    func.call @srand(%i)
    %next: i32 = int.add.nsw %i, %one
    cf.continue %next
  }
  func.ret
}

func @zeros() {
  %a: i128, %b: b32, %c: ptr = func.call @wide()
  func.ret
}

func @dangling() {
  %t: i1 = int.const 1
  %p: ptr = cf.if %t {
    %s: ptr = mem.stack 4, align 4
    cf.yield %s
  } else {
    %n: ptr = ptr.null
    cf.yield %n
  }
  func.call @free_like(%p)
  func.ret
}

func @poison_ptr(%p: ptr) {
  func.call @free_like(%p)
  func.ret
}
