// External functions take scalars, even in HFIR: their ABI is not decided yet.
// error: extern @x: struct<C>{i8} is not a value type
extern func @x(struct<C>{i8}) effects[] assume
func @f() {
  func.ret
}
