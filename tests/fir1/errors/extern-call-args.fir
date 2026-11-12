// error: arguments of @puts: expected (ptr) but got (i32)
extern func @puts(ptr) -> i32 effects[read(args)] assume

func @f(%x: i32) -> i32 {
  %r: i32 = func.call @puts(%x)
  func.ret %r
}
