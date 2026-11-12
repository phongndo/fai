// Lowering computes an in-bounds element offset exactly at twice the address size, which needs
// the stride to fit the address size; only alignments bigger than the address space break that.
// lower-error: in @f: @1:1: cannot lower: the stride of i8, 512, doesn't fit an i8
memspace default ptr 8 addr 8 int 8:512 16:2 32:4 64:8 128:16

func @f(%p: ptr, %i: i8) -> ptr {
  %q: ptr = ptr.index.inbounds i8 %p, %i @1:1
  func.ret %q
}

// run: @f(null, 0) -> returned ptr null
