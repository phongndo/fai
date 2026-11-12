// error: in @f: @3:3: this op has no results
func @f(%p: ptr, %x: i32) {
  %r: i32 = mem.store i32 %x, %p, align 4 @3:3
  func.ret
}
