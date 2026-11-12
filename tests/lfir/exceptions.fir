// The exception slot (decision: Exceptions at run time): a throwing function makes its
// exception pending (`aarch64.exn.set`) and returns; a caller checks after the call
// (`aarch64.b.exn`) and takes it (`aarch64.exn.take`), or returns with it still pending. The
// outermost call returning with one pending ends the run with `threw`.
// run: @raise(1) -> threw ptr #1
// run: @raise(0) -> returned i32 0
// run: @pass(1) -> threw ptr #1
// run: @pass(5) -> returned i32 6
// run: @catch(1) -> returned i32 7
// run: @catch(5) -> returned i32 5
// run: @take_nothing() -> stuck @9:5: no exception is pending
layer lfir aarch64

global @err: i32 = 7

func @raise(%k: i32) -> i32 {
  aarch64.code {
  ^entry:
    aarch64.subs.imm.w xzr, x0, 1
    aarch64.b.eq ^throw, ^ok
  ^throw:
    aarch64.adrl x1, @err
    aarch64.exn.set x1
    aarch64.ret
  ^ok:
    aarch64.ret
  }
}

func @pass(%k: i32) -> i32 {
  aarch64.code {
  ^entry:
    aarch64.bl @raise
    aarch64.b.exn ^out, ^more
  ^more:
    aarch64.add.imm.w x0, x0, 1
    aarch64.ret
  ^out:
    aarch64.ret
  }
}

func @catch(%k: i32) -> i32 {
  aarch64.code {
  ^entry:
    aarch64.bl @raise
    aarch64.b.exn ^land, ^done
  ^land:
    aarch64.exn.take x2
    aarch64.ldr.w x0, x2, 0
    aarch64.ret
  ^done:
    aarch64.ret
  }
}

func @take_nothing() -> i32 {
  aarch64.code {
  ^entry:
    aarch64.exn.take x0 @9:5
    aarch64.ret
  }
}
