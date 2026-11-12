// Lowering turns `ptr.field` into `ptr.offset` by the field's offset as an address-sized
// integer, read signed: an offset of half the address space or more can't be lowered exactly.
// lower-error: in @f: @1:1: cannot lower: field 1 of struct<C>{array<200 x i8>, i8} is at offset 200, which doesn't fit a signed i8
memspace default ptr 8 addr 8

func @f(%p: ptr) -> ptr {
  %q: ptr = ptr.field.inbounds struct<C>{array<200 x i8>, i8} %p, 1 @1:1
  func.ret %q
}

// run: @f(null) -> returned ptr poison
