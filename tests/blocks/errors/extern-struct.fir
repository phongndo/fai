// External functions take scalars and C ABI composites (structs and arrays), not slices.
// error: extern @x: slice is not a value type
extern func @x(slice) effects[] assume
func @f() {
  func.ret
}
