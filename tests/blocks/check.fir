// `cf.check.REASON %ok` is what the HFIR checks lower to, and is a core op in HFIR and MFIR:
// nothing if `%ok` is 1, a trap with the reason if it is 0, UB if it is `poison`.
layer mfir

func @check(%ok: i1) {
  cf.check.bounds %ok @1:1
  cf.check.tag %ok @2:1
  cf.check.overflow %ok @3:1
  func.ret
}

func @reasons(%k: i8) {
  %z: i1 = int.const 0 @4:1
  %c: i8 = int.const 0 @5:1
  %is0: i1 = int.cmp.eq %k, %c @6:1
  cf.if %is0 {
    cf.check.div0 %z @7:1
    cf.yield
  } else {
    cf.yield
  }
  cf.check.shift %z @8:1
  func.ret
}

// run: @check(1) -> returned
// run: @check(0) -> trap bounds @1:1
// run: @check(poison) -> ub poison @1:1 (check of poison)
// run: @reasons(0) -> trap div0 @7:1
// run: @reasons(1) -> trap shift @8:1
