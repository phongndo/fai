// Code returns with aarch64.ret; func.ret ends only a plain function body.
// error: func.ret can't be inside aarch64.code
layer lfir aarch64

func @f() {
  aarch64.code {
  ^entry:
    func.ret
  }
}
