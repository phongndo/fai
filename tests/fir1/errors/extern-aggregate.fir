// External functions take structs and arrays (as the C ABI passes them), but not unions.
// error: extern @f: union<i32, i64> is not a value type
extern func @f(union<i32, i64>) effects[] assume
