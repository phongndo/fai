// Heap memory from allocator families, and every way to misuse it.
// run: @heap(7) -> returned i32 7
// run: @use_after_free() -> ub use-after-free @3:3 (allocated at @1:3, freed at @2:3)
// run: @double_free() -> ub double-free @3:3 (allocated at @1:3, freed at @2:3)
// run: @wrong_family() -> ub bad-free @2:3 (allocated at @1:3 by c.malloc)
// run: @interior() -> ub bad-free @2:3 (offset 4 is not the start of the allocation)
// run: @free_stack() -> ub bad-free @2:3 (allocated at @1:3 by mem.stack)
// run: @free_null() -> returned
// Memory still allocated when the program ends is reported with where it came from.
// run: @leak() -> returned; leak: 8 bytes from c.malloc at @1:3
func @heap(%x: i32) -> i32 {
  %n: i64 = int.const 4
  %p: ptr = mem.alloc.null c.malloc %n, align 16
  mem.store i32 %x, %p, align 4
  %y: i32 = mem.load %p, align 4
  mem.free c.malloc %p
  func.ret %y
}

func @use_after_free() -> i32 {
  %n: i64 = int.const 4
  %p: ptr = mem.alloc.null c.malloc %n, align 16 @1:3
  mem.free c.malloc %p @2:3
  %y: i32 = mem.load %p, align 4 @3:3
  func.ret %y
}

func @double_free() {
  %n: i64 = int.const 4
  %p: ptr = mem.alloc.null c.malloc %n, align 16 @1:3
  mem.free c.malloc %p @2:3
  mem.free c.malloc %p @3:3
  func.ret
}

func @wrong_family() {
  %n: i64 = int.const 4
  %p: ptr = mem.alloc.null c.malloc %n, align 16 @1:3
  mem.free cpp.delete %p @2:3
  func.ret
}

func @interior() {
  %n: i64 = int.const 8
  %p: ptr = mem.alloc.trap rust.alloc %n, align 8 @1:3
  %four: i64 = int.const 4
  %q: ptr = ptr.offset.inbounds %p, %four
  mem.free rust.alloc %q @2:3
  func.ret
}

func @free_stack() {
  %p: ptr = mem.stack 4, align 4 @1:3
  mem.free c.malloc %p @2:3
  func.ret
}

func @free_null() {
  %p: ptr = ptr.null
  mem.free c.malloc %p
  func.ret
}

func @leak() {
  %n: i64 = int.const 8
  %p: ptr = mem.alloc.null c.malloc %n, align 16 @1:3
  func.ret
}
