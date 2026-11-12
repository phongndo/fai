// An external function's struct or array result is its only one, in every layer.
// error: extern @f: array<2 x i32> can't be one of several results: outside HFIR, a struct or array result is the only one
extern func @f() -> (array<2 x i32>, i8) effects[] assume
