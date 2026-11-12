// Variadic functions defined in FIR (decisions: Varargs, va_list): a call passes its fixed
// arguments, then `...`, then variadic arguments of any type a register holds; `va.start` puts a
// cursor in a `va_list`, and `va.arg` reads the arguments one by one as its result type.

// run: @sum(0) -> returned i64 0
// run: @sum(3, i64 1, i64 2, i64 3) -> returned i64 6
// run: @sum(2, i32 -1, i64 5) -> returned i64 poison
// run: @mixed() -> returned i64 21, f64 7.5
// run: @many() -> returned i64 120, f64 60.0
// run: @ptrs() -> returned i32 42
// run: @copy() -> returned i64 32
// run: @pass() -> returned i64 30
// run: @nested() -> returned i64 15
// run: @narrow() -> returned i64 -1, i64 poison, f32 2.5, i8 -1
// run: @start_twice() -> returned i64 2
// run: @in_struct() -> returned i64 9
func @sum(%n: i32, ...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 1
  va.start %ap
  %zero: i64 = int.const 0
  %izero: i32 = int.const 0
  %r: i64 = cf.loop iter(%i: i32 = %izero, %acc: i64 = %zero) {
    %done: i1 = int.cmp.sge %i, %n
    cf.if %done {
      cf.break %acc
    }
    %x: i64 = va.arg %ap
    %acc2: i64 = int.add.wrap %acc, %x
    %one: i32 = int.const 1
    %i2: i32 = int.add.wrap %i, %one
    cf.continue %i2, %acc2
  }
  va.end %ap
  func.ret %r
}

// Integers and floats interleaved: each class keeps its own count.
func @mix(%n: i32, ...) -> (i64, f64) {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = va.arg %ap
  %x: f64 = va.arg %ap
  %b: i64 = va.arg %ap
  %y: f64 = va.arg %ap
  %c: i64 = va.arg %ap
  %ab: i64 = int.add.wrap %a, %b
  %abc: i64 = int.add.wrap %ab, %c
  %xy: f64 = float.add %x, %y
  va.end %ap
  func.ret %abc, %xy
}

func @mixed() -> (i64, f64) {
  %n: i32 = int.const 5
  %a: i64 = int.const 1
  %x: f64 = float.const 2.5
  %b: i64 = int.const 4
  %y: f64 = float.const 5.0
  %c: i64 = int.const 16
  %r: i64, %s: f64 = func.call @mix(%n, ... %a, %x, %b, %y, %c)
  func.ret %r, %s
}

// More than eight of each class: the rest go on the stack.
func @sum_both(%n: i32, ...) -> (i64, f64) {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %zero: i64 = int.const 0
  %fzero: f64 = float.const 0.0
  %izero: i32 = int.const 0
  %r: i64, %f: f64 = cf.loop iter(%i: i32 = %izero, %acc: i64 = %zero, %facc: f64 = %fzero) {
    %done: i1 = int.cmp.sge %i, %n
    cf.if %done {
      cf.break %acc, %facc
    }
    %x: i64 = va.arg %ap
    %y: f64 = va.arg %ap
    %acc2: i64 = int.add.wrap %acc, %x
    %facc2: f64 = float.add %facc, %y
    %one: i32 = int.const 1
    %i2: i32 = int.add.wrap %i, %one
    cf.continue %i2, %acc2, %facc2
  }
  va.end %ap
  func.ret %r, %f
}

func @many() -> (i64, f64) {
  %n: i32 = int.const 15
  %a: i64 = int.const 8
  %x: f64 = float.const 4.0
  %r: i64, %s: f64 = func.call @sum_both(%n, ... %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x, %a, %x)
  func.ret %r, %s
}

// Pointers keep their provenance through the variadic arguments.
func @deref(...) -> i32 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %p: ptr = va.arg %ap
  %v: i32 = mem.load %p, align 4
  func.ret %v
}

func @ptrs() -> i32 {
  %p: ptr = mem.stack.of i32, align 4
  %v: i32 = int.const 42
  mem.store i32 %v, %p, align 4
  %r: i32 = func.call @deref(... %p)
  func.ret %r
}

// `va_copy` is a copy of the va_list's bytes: the copy reads on from where the original was.
func @twice(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  %aq: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = va.arg %ap
  mem.copy va_list %aq, %ap, align 8
  %b: i64 = va.arg %ap
  %c: i64 = va.arg %aq
  %d: i64 = va.arg %aq
  va.end %aq
  va.end %ap
  %bc: i64 = int.add.wrap %b, %c
  %r: i64 = int.add.wrap %bc, %d
  %ra: i64 = int.add.wrap %r, %a
  func.ret %ra
}

func @copy() -> i64 {
  %a: i64 = int.const 1
  %b: i64 = int.const 10
  %c: i64 = int.const 11
  %r: i64 = func.call @twice(... %a, %b, %c)
  func.ret %r
}

// A va_list passed to another function, which reads on from where the caller was.
func @rest(%ap: ptr) -> i64 {
  %x: i64 = va.arg %ap
  %y: i64 = va.arg %ap
  %r: i64 = int.add.wrap %x, %y
  func.ret %r
}

func @first_then_rest(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %skip: i64 = va.arg %ap
  %r: i64 = func.call @rest(%ap)
  va.end %ap
  func.ret %r
}

func @pass() -> i64 {
  %a: i64 = int.const 100
  %b: i64 = int.const 10
  %c: i64 = int.const 20
  %r: i64 = func.call @first_then_rest(... %a, %b, %c)
  func.ret %r
}

// A variadic function calling another with its own variadic arguments.
func @outer(%n: i32, ...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = va.arg %ap
  %b: i64 = va.arg %ap
  %two: i32 = int.const 2
  %s: i64 = func.call @sum(%two, ... %a, %b)
  %c: i64 = va.arg %ap
  va.end %ap
  %r: i64 = int.add.wrap %s, %c
  func.ret %r
}

func @nested() -> i64 {
  %n: i32 = int.const 3
  %a: i64 = int.const 4
  %b: i64 = int.const 5
  %c: i64 = int.const 6
  %r: i64 = func.call @outer(%n, ... %a, %b, %c)
  func.ret %r
}

// Narrow arguments take a slot's low bytes; reading more than was passed gives poison for the
// rest, as a register's unspecified high bits.
func @widths(...) -> (i64, i64, f32, i8) {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = va.arg %ap
  %b: i64 = va.arg %ap
  %c: f32 = va.arg %ap
  %d: i8 = va.arg %ap
  func.ret %a, %b, %c, %d
}

func @narrow() -> (i64, i64, f32, i8) {
  %a: i64 = int.const -1
  %b: i32 = int.const 7
  %c: f32 = float.const 2.5
  %d: i64 = int.const 255
  %w: i64, %x: i64, %y: f32, %z: i8 = func.call @widths(... %a, %b, %c, %d)
  func.ret %w, %x, %y, %z
}

// va.start again restarts at the first argument.
func @restart(...) -> i64 {
  %ap: ptr = mem.stack.of va_list, align 8
  va.start %ap
  %a: i64 = va.arg %ap
  %b: i64 = va.arg %ap
  va.start %ap
  %c: i64 = va.arg %ap
  %r: i64 = int.add.wrap %a, %c
  func.ret %r
}

func @start_twice() -> i64 {
  %a: i64 = int.const 1
  %b: i64 = int.const 7
  %r: i64 = func.call @restart(... %a, %b)
  func.ret %r
}

// A va_list can be a struct field.
func @field(...) -> i64 {
  %s: ptr = mem.stack.of struct<C>{i32, va_list}, align 1
  %ap: ptr = ptr.field.inbounds struct<C>{i32, va_list} %s, 1
  va.start %ap
  %a: i64 = va.arg %ap
  %b: i64 = va.arg %ap
  %r: i64 = int.add.wrap %a, %b
  func.ret %r
}

func @in_struct() -> i64 {
  %a: i64 = int.const 4
  %b: i64 = int.const 5
  %r: i64 = func.call @field(... %a, %b)
  func.ret %r
}
