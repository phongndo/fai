// error: in @f: @2:3: a block must end with a terminator
// There is no fall-through between blocks: C's fall-through is a cf.br to the next block.
func @f() {
  cf.blocks @2:3 {
  ^a:
    %z: i32 = int.const 0
  ^b:
    cf.yield
  }
  func.ret
}
