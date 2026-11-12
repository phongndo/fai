// func.addr names a function.
// error: in @f: @?: no function @g
global @g: i32 = 0

func @f() -> ptr {
  %p: ptr = func.addr @g
  func.ret %p
}
