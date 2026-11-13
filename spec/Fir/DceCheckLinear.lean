import Fir.DceCheck
import Std.Data.HashMap.Lemmas

/-!
# The DCE checker without the quadratic scan, and for whole modules

`checkFunc` (`Fir.DceCheck`) is the proved checker, but it is quadratic in a function's size:
for each op it deletes, `deletable` scans the rest of the region in the target for readers
(`opsReads`). `checkFuncL` decides the same thing in time linear in the function's size times
its nesting depth (by construction, with hash-map operations at their expected cost; not proved). It keeps, for the target ops not yet matched, how many times each name is
read at any depth (`Counts`); a deleted op's results must have count zero, and matching a
target op takes its reads off. `checkFuncL_eq` proves it *equal* to `checkFunc`, so
`checkFunc_sound` holds for it unchanged, and nothing about the checker's verdicts changes:
only its cost.

`checkModule` is the checker `fir-ref check-dce` runs on two modules: the same functions, in the
same order, with the same names and source files, each target function accepted. Before, that
pairing was unproved glue in `Main.lean`. `checkModule_sound` says what an acceptance gives, per
name by `Module.find?` (the first function of that name; the interpreter's calls take the last,
which is the same function in a verified module, whose names are unique): for every name, the target has a function by
that name exactly when the source has one, and if the source's is `Decided` in the source module,
the target's refines it there.

What it does not give: that the target *module* refines the source module. Each target function
is related to its source in the source module (its calls go to the source's callees); running the
target module calls target functions. Composing the per-function results is open
(`docs/assurance/README.md`, remaining obligation 3). Nor does it check `Decided`.
-/

namespace Fir.Dce

/-! ## Counting reads -/

/-- How many times an operand reads `%n`: once, if it is the variable `%n`. -/
def operandCount (n : String) : Operand → Nat
  | .var m => if m == n then 1 else 0
  | .hole .. => 0

def argsCount (n : String) : List Operand → Nat
  | [] => 0
  | a :: as => operandCount n a + argsCount n as

mutual
/-- How many times an op reads `%n`, at any depth. -/
def opReadCount (n : String) : Op → Nat
  | .mk _ _ args rs _ => argsCount n args + regionsReadCount n rs

def regionsReadCount (n : String) : List Region → Nat
  | [] => 0
  | .mk _ ops _ :: rs => opsReadCount n ops + regionsReadCount n rs

def opsReadCount (n : String) : List Op → Nat
  | [] => 0
  | o :: os => opReadCount n o + opsReadCount n os
end

theorem argsCount_eq_zero (n : String) : ∀ (as : List Operand),
    (argsCount n as == 0) = !as.any (Operand.reads n)
  | [] => rfl
  | .var m :: as => by
    have := argsCount_eq_zero n as
    by_cases h : m = n <;> simp_all [argsCount, operandCount, Operand.reads]
  | .hole .. :: as => by
    have := argsCount_eq_zero n as
    simp_all [argsCount, operandCount, Operand.reads]

theorem add_beq_zero (a b : Nat) : (a + b == 0) = ((a == 0) && (b == 0)) := by
  rw [Bool.eq_iff_iff]; simp [Nat.add_eq_zero_iff]

mutual
theorem opReadCount_eq_zero (n : String) : ∀ (o : Op), (opReadCount n o == 0) = !o.reads n
  | .mk _ _ args rs _ => by
    rw [opReadCount, Op.reads, Bool.not_or, ← argsCount_eq_zero n args,
      ← regionsReadCount_eq_zero n rs, add_beq_zero]

theorem regionsReadCount_eq_zero (n : String) : ∀ (rs : List Region),
    (regionsReadCount n rs == 0) = !regionsReads n rs
  | [] => rfl
  | .mk _ ops _ :: rs => by
    rw [regionsReadCount, regionsReads, Bool.not_or, ← opsReadCount_eq_zero n ops,
      ← regionsReadCount_eq_zero n rs, add_beq_zero]

theorem opsReadCount_eq_zero (n : String) : ∀ (os : List Op),
    (opsReadCount n os == 0) = !opsReads n os
  | [] => rfl
  | o :: os => by
    rw [opsReadCount, opsReads, Bool.not_or, ← opReadCount_eq_zero n o,
      ← opsReadCount_eq_zero n os, add_beq_zero]
end

/-! ## The counts, kept in a hash map -/

/-- For each name, how many times the ops still to be matched read it (absent: zero). -/
abbrev Counts := Std.HashMap String Nat

/-- `φ` applied `k` times. -/
def iter (φ : Nat → Nat) : Nat → Nat → Nat
  | 0, a => a
  | k + 1, a => iter φ k (φ a)

theorem iter_add (φ : Nat → Nat) : ∀ (j k a : Nat), iter φ (j + k) a = iter φ k (iter φ j a)
  | 0, k, a => by simp [iter]
  | j + 1, k, a => by
    rw [Nat.add_right_comm, iter, iter, iter_add φ j k]

theorem iter_succ : ∀ (k a : Nat), iter Nat.succ k a = a + k
  | 0, a => rfl
  | k + 1, a => by rw [iter, iter_succ k]; omega

theorem iter_pred : ∀ (k a : Nat), iter Nat.pred k a = a - k
  | 0, a => rfl
  | k + 1, a => by rw [iter, iter_pred k, Nat.pred_eq_sub_one]; omega

/-- Apply `φ` to the count of `%m`. -/
def tick (φ : Nat → Nat) (M : Counts) (m : String) : Counts := M.insert m (φ (M.getD m 0))

theorem tick_getD (φ : Nat → Nat) (M : Counts) (m n : String) :
    (tick φ M m).getD n 0 = if m == n then φ (M.getD n 0) else M.getD n 0 := by
  simp only [tick, Std.HashMap.getD_insert]
  split <;> simp_all

def argsTick (φ : Nat → Nat) : List Operand → Counts → Counts
  | [], M => M
  | .var m :: as, M => argsTick φ as (tick φ M m)
  | .hole .. :: as, M => argsTick φ as M

mutual
/-- Apply `φ` to the count of each name `o` reads, once per read, at any depth. -/
def opTick (φ : Nat → Nat) : Op → Counts → Counts
  | .mk _ _ args rs _, M => regionsTick φ rs (argsTick φ args M)

def regionsTick (φ : Nat → Nat) : List Region → Counts → Counts
  | [], M => M
  | .mk _ ops _ :: rs, M => regionsTick φ rs (opsTick φ ops M)

def opsTick (φ : Nat → Nat) : List Op → Counts → Counts
  | [], M => M
  | o :: os, M => opsTick φ os (opTick φ o M)
end

theorem argsTick_getD (φ : Nat → Nat) (n : String) : ∀ (as : List Operand) (M : Counts),
    (argsTick φ as M).getD n 0 = iter φ (argsCount n as) (M.getD n 0)
  | [], M => rfl
  | .var m :: as, M => by
    rw [argsTick, argsTick_getD φ n as, tick_getD, argsCount, iter_add]
    by_cases h : m = n <;> simp_all [operandCount, iter]
  | .hole .. :: as, M => by
    rw [argsTick, argsTick_getD φ n as, argsCount]
    simp [operandCount]

mutual
theorem opTick_getD (φ : Nat → Nat) (n : String) : ∀ (o : Op) (M : Counts),
    (opTick φ o M).getD n 0 = iter φ (opReadCount n o) (M.getD n 0)
  | .mk _ _ args rs _, M => by
    rw [opTick, regionsTick_getD φ n rs, argsTick_getD φ n args, opReadCount, iter_add]

theorem regionsTick_getD (φ : Nat → Nat) (n : String) : ∀ (rs : List Region) (M : Counts),
    (regionsTick φ rs M).getD n 0 = iter φ (regionsReadCount n rs) (M.getD n 0)
  | [], M => rfl
  | .mk _ ops _ :: rs, M => by
    rw [regionsTick, regionsTick_getD φ n rs, opsTick_getD φ n ops, regionsReadCount, iter_add]

theorem opsTick_getD (φ : Nat → Nat) (n : String) : ∀ (os : List Op) (M : Counts),
    (opsTick φ os M).getD n 0 = iter φ (opsReadCount n os) (M.getD n 0)
  | [], M => rfl
  | o :: os, M => by
    rw [opsTick, opsTick_getD φ n os, opTick_getD φ n o, opsReadCount, iter_add]
end

/-- The counts of every name `ops` read. -/
def countReads (ops : List Op) : Counts := opsTick Nat.succ ops ∅

/-- `M` holds exactly the read counts of `t`. -/
def Counts.Rep (M : Counts) (t : List Op) : Prop := ∀ n, M.getD n 0 = opsReadCount n t

theorem countReads_rep (ops : List Op) : (countReads ops).Rep ops := by
  intro n
  simp [countReads, opsTick_getD, iter_succ]

theorem Counts.Rep.tail {M : Counts} {o : Op} {t : List Op} (h : M.Rep (o :: t)) :
    (opTick Nat.pred o M).Rep t := by
  intro n
  rw [opTick_getD, iter_pred, h n, opsReadCount]
  omega

/-! ## The checker -/

/-- `deletable`, reading the target's counts instead of scanning it. -/
def deletableC (M : Counts) (o : Op) : Bool :=
  match o with
  | .mk k res args rs _ =>
    dcePerm k == .delete && rs.isEmpty &&
      args.all (fun | .var _ => true | .hole .. => false) &&
      res.all (fun r => M.getD r.name 0 == 0)

theorem deletableC_eq {M : Counts} {t : List Op} (h : M.Rep t) (o : Op) :
    deletableC M o = deletable o t := by
  have h' : ∀ n, M.getD n 0 = opsReadCount n t := h
  obtain ⟨k, res, args, rs, loc⟩ := o
  simp only [deletableC, deletable, h', opsReadCount_eq_zero]
  rfl

mutual
/-- `checkOp`, with `checkOpsL` for the regions. -/
def checkOpL : Op → Op → Bool
  | .mk k res args rt loc, .mk k' res' args' rs loc' =>
    decide (k = k') && decide (res = res') && decide (args = args') && decide (loc = loc') &&
      checkRegionsL rt rs

def checkRegionsL : List Region → List Region → Bool
  | [], [] => true
  | .mk ps ot lbl :: rt, .mk ps' os lbl' :: rs =>
    decide (ps = ps') && decide (lbl = lbl') && checkOpsL (countReads ot) ot os &&
      checkRegionsL rt rs
  | _, _ => false

/-- `checkOps`, given the read counts `M` of the target ops `t` still to be matched. -/
def checkOpsL : Counts → List Op → List Op → Bool
  | _, [], [] => true
  | M, o' :: t', o :: s =>
    if checkOpL o' o then checkOpsL (opTick Nat.pred o' M) t' s
    else deletableC M o && checkOpsL M (o' :: t') s
  | M, [], o :: s => deletableC M o && checkOpsL M [] s
  | _, _ :: _, [] => false
end

mutual
theorem checkOpL_eq : ∀ (ot os : Op), checkOpL ot os = checkOp ot os
  | .mk k res args rt loc, .mk k' res' args' rs loc' => by
    rw [checkOpL, checkOp, checkRegionsL_eq rt rs]

theorem checkRegionsL_eq : ∀ (rt rs : List Region), checkRegionsL rt rs = checkRegions rt rs
  | [], [] => rfl
  | .mk ps ot lbl :: rt, .mk ps' os lbl' :: rs => by
    rw [checkRegionsL, checkRegions, checkOpsL_eq (countReads ot) ot os (countReads_rep ot),
      checkRegionsL_eq rt rs]
  | [], _ :: _ => rfl
  | .mk .. :: _, [] => rfl

theorem checkOpsL_eq : ∀ (M : Counts) (t s : List Op), M.Rep t → checkOpsL M t s = checkOps t s
  | _, [], [], _ => rfl
  | M, o' :: t', o :: s, h => by
    rw [checkOpsL, checkOps, checkOpL_eq o' o, deletableC_eq h,
      checkOpsL_eq _ t' s h.tail, checkOpsL_eq M (o' :: t') s h]
  | M, [], o :: s, h => by
    rw [checkOpsL, checkOps, deletableC_eq h, checkOpsL_eq M [] s h]
  | _, _ :: _, [], _ => rfl
end

/-- `checkFunc`, with read counts instead of a scan per deleted op. -/
def checkFuncL (tgt src : Func) : Bool :=
  decide (tgt.params = src.params) && decide (tgt.rets = src.rets) &&
    decide (tgt.variadic = src.variadic) &&
      checkOpsL (countReads tgt.body.ops) tgt.body.ops src.body.ops

/-- **The counting DCE checker is the proved checker.** `checkFuncL`, which `fir-ref check-dce`
runs, gives the same verdict as `checkFunc` on every pair of functions, so `checkFunc_sound`
holds for it. -/
theorem checkFuncL_eq (tgt src : Func) : checkFuncL tgt src = checkFunc tgt src := by
  rw [checkFuncL, checkFunc, checkOpsL_eq _ _ _ (countReads_rep _)]

theorem checkFuncL_sound {mod : Module} {tgt src : Func} (h : checkFuncL tgt src = true)
    (dec : src.Decided mod) : tgt.Refines mod src :=
  checkFunc_sound (checkFuncL_eq tgt src ▸ h) dec

/-! ## Modules -/

/-- Functions `ts` and `ss` pairwise: the same name and source file, and accepted. -/
def checkFuncs : List Func → List Func → Bool
  | [], [] => true
  | t :: ts, s :: ss =>
    t.name == s.name && t.file == s.file && checkFuncL t s && checkFuncs ts ss
  | _, _ => false

/-- The DCE checker for modules: the target's functions are the source's, in order, by name
and source file, each accepted by `checkFuncL`. (What lies outside functions is not looked at:
`checkModule_sound` relates each target function to its source in the source module, which
doesn't involve the target's globals or externs.) -/
def checkModule (tgt src : Module) : Bool := checkFuncs tgt.funcs src.funcs

theorem _root_.Option.Rel.mono {r r' : α → β → Prop} (h : ∀ a b, r a b → r' a b) :
    ∀ {x : Option α} {y : Option β}, Option.Rel r x y → Option.Rel r' x y
  | _, _, .none => .none
  | _, _, .some hab => .some (h _ _ hab)

theorem checkFuncs_find {name : String} : ∀ {ts ss : List Func}, checkFuncs ts ss = true →
    Option.Rel (fun t s => checkFunc t s = true)
      (ts.find? (·.name == name)) (ss.find? (·.name == name))
  | [], [], _ => .none
  | t :: ts, s :: ss, h => by
    simp only [checkFuncs, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hn, _⟩, hc⟩, hr⟩ := h
    simp only [List.find?_cons, hn]
    split
    · exact .some (checkFuncL_eq t s ▸ hc)
    · exact checkFuncs_find hr
  | [], _ :: _, h => by simp [checkFuncs] at h
  | _ :: _, [], h => by simp [checkFuncs] at h

/-- **The module DCE checker is sound, function by function.** If `checkModule` (what
`fir-ref check-dce` runs) accepts, then for every name, the target module has a function by
that name exactly when the source module does, and the target's refines the source's in the
source module whenever the source's is `Decided` there. -/
theorem checkModule_sound {tgt src : Module} (h : checkModule tgt src = true) (name : String) :
    Option.Rel (fun t s => s.Decided src → t.Refines src s) (tgt.find? name) (src.find? name) := by
  exact Option.Rel.mono (fun _ _ hc dec => checkFunc_sound hc dec) (checkFuncs_find h)

end Fir.Dce
