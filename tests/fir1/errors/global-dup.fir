// Globals and functions share one namespace.
// error: function @f is defined more than once
global @f: i32 = 0

func @f() {
  func.ret
}
