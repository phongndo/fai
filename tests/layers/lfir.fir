// An LFIR module for AArch64. LFIR allows its target's dialect (`aarch64.*`, declared in a later
// round) and, of the core ops, only `func.ret`, which ends a function. Globals and external
// functions are module structure, not ops, so every layer has them.
// run: @id(5) -> returned i32 5
// run: @none() -> returned
layer lfir aarch64

global @g: i32 = 7
extern func @puts(ptr) -> i32 effects[read(args)] assume

func @id(%x: i32) -> i32 {
  func.ret %x
}

func @none() {
  func.ret
}
