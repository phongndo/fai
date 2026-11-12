// Unions have no layout, so they are not loaded or stored.
// error: @1:1: union<i8, i32> can't be loaded: it has no layout
func @f(%p: ptr) {
  %u: union<i8, i32> = mem.load %p, align 4 @1:1
  func.ret
}
