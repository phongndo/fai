// copy gives its operand's value, of any type, poison included.
// run: @int(7) -> returned i32 7
// run: @int(poison) -> returned i32 poison
// run: @ptr(null) -> returned ptr null
// run: @ptr(poison) -> returned ptr poison
// Forwarding a store to the next load gives a copy of the stored value.
// run: @forwarded(42) -> returned i32 42
func @int(%x: i32) -> i32 {
  %y: i32 = copy %x
  func.ret %y
}

func @ptr(%p: ptr) -> ptr {
  %q: ptr = copy %p
  func.ret %q
}

func @forwarded(%x: i32) -> i32 {
  %p: ptr = mem.stack 4, align 4
  mem.store i32 %x, %p, align 4
  %y: i32 = copy %x
  func.ret %y
}
