// A type must fit the address space.
// error: in @f: @?: array<1073741824 x i32> is too large for the address space
memspace default ptr 32 addr 32

func @f() -> i32 {
  %n: i32 = ty.size array<1073741824 x i32>
  func.ret %n
}
