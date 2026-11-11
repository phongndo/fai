// An address can carry several exposed tags of one allocation. The intended rule picks the tag
// that avoids UB; until it is implemented, the reference tool reports `ambiguous` when the choice
// matters, rather than picking one and maybe reporting UB the intended rule wouldn't.
// Here %r's address carries %p's tag and %q's; the noalias scope of %p tells them apart.
// run: @caller(5) -> ambiguous @1:3 (address 4096 may carry tag 1 or 2 of #1, and an active noalias or readonly scope tells them apart)
// Without a scope that tells them apart, the choice doesn't matter.
// run: @no_scope(5) -> returned i32 5
func @callee(%p: ptr [noalias assume], %q: ptr) -> i32 {
  %x: i32 = mem.load %p, align 4
  %ep: i64 = ptr.expose %p
  %eq: i64 = ptr.expose %q
  %r: ptr = ptr.from_exposed %ep
  %one: i32 = int.const 1
  mem.store i32 %one, %r, align 4 @1:3
  func.ret %x
}

func @caller(%v: i32) -> i32 {
  %a: ptr = mem.stack 4, align 4
  mem.store i32 %v, %a, align 4
  %x: i32 = func.call @callee(%a, %a)
  func.ret %x
}

func @expose_it(%p: ptr [noalias assume]) {
  %e: i64 = ptr.expose %p
  func.ret
}

// After the call, %a's address carries two tags but no scope is active.
func @no_scope(%v: i32) -> i32 {
  %a: ptr = mem.stack 4, align 4
  func.call @expose_it(%a)
  %e: i64 = ptr.expose %a
  %r: ptr = ptr.from_exposed %e
  mem.store i32 %v, %r, align 4
  %x: i32 = mem.load %a, align 4
  func.ret %x
}
