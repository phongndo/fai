// The layer is checked in nested regions and for the generic form too.
// error: in @f: @9:7: ptr.index.wrap is not allowed in layer mfir; it is allowed in hfir
layer mfir

func @f(%c: i1, %i: i64) {
  %p: ptr = mem.stack 16, align 4
  cf.if %c {
    cf.loop {
      %e: ptr = "ptr.index.wrap"(%p, %i) {ty = i32} @9:7
      cf.break
    }
    cf.yield
  }
  func.ret
}
