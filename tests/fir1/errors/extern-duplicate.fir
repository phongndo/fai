// error: function @f is defined more than once
extern func @f() effects[] assume

func @f() {
  func.ret
}
