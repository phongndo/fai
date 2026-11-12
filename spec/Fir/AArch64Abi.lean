import Fir.AArch64Syntax
import Fir.Layout
import Fir.MemRules

/-!
# AAPCS64: where values travel

The procedure call standard for the Arm 64-bit architecture (AAPCS64, §6.8 "Parameter passing"
and §6.9 "Result return") as FIR uses it on Linux (decisions: Calling convention, C ABI for
aggregates). The LFIR machine (`Fir.AArch64Machine`), instruction selection, and the register
allocator (`abi.rs`, its twin) all ask here, so a C caller and FIR agree on which bytes are in
which register or stack slot.

**Classes.** A scalar is `gp` (an integer, bytes, or a pointer, in an `x` register) or `fp` (a
float, in a `d` or `s` register). A composite (`Ty.isComposite`: a struct or an array) is
* nothing if its size is 0 (GCC and Clang ignore empty structs in C);
* a *homogeneous floating-point aggregate* (HFA, `hfaOf?`) if its leaves are one to four floats
  of one format that tile it in memory (in any declared order: memory order is what counts), and
  it has no zero-length array (GCC's rule; empty structs don't count): its members travel in
  consecutive FP registers, one each, in memory order;
* otherwise, up to 16 bytes: its bytes travel in one or two `x` registers, 8 per register, as
  `ldr`s from a double-word-aligned copy would load them (`words`), the first register even if
  the composite is 16-byte aligned (C.10);
* otherwise a pointer to a copy the caller makes (`ref`, B.4), which travels as a `gp` scalar.

**Arguments** (`argLocs`): stage C's rules in order, with NGRN, NSRN, and NSAA. An HFA that
doesn't fit the FP registers left sets NSRN to 8 (C.3) and goes on the stack as its bytes; a
composite that doesn't fit the `x` registers left sets NGRN to 8 (C.13) and goes on the stack at
NSAA rounded up to its alignment (at least 8; C.14), its size rounded up to 8 (B.5). Scalars on
the stack take 8-byte slots (C.16).

**Results** (`resRegs`): a composite comes back where it would be passed as the first argument
(HFA in `d0`…, up to 16 bytes in `x0`, `x1`); a larger one in memory the caller passes in `x8`.
Scalars keep FIR's rule (decision: Calling convention): one or two in `d0`, `d1` if all are
floats of one format, otherwise `x0`, `x1`; three or more in 8-byte slots at `x8`.

**Bytes and registers.** A composite's bytes (its leaves' encodings at their offsets, `poison`
in padding) split into register pieces (`pieces`): 8-byte words, or an HFA's members. A piece
is a register's low bytes (`Word.ofBytes?`, `Word.bytes`). `pieces_flatten` and `roundTrip`
prove the round trip for pieces that are wholly defined: bytes split into pieces, each put in a
register and read back, are the bytes; a word of eight fragments of one pointer is that pointer,
so provenance survives. `arrives` drops the premise: for any words that hold the pieces
(`Word.Holds`, as the machine's word for a piece does whatever it picks for `poison` and stray
fragments, `Word.holds_fill`), every defined byte comes back in place, padding or `poison`
leaves notwithstanding. A pointer leaf keeps its provenance when it fills a word
(`ptrLeaf_inReg`); one that doesn't (`Ty.splitsPtr`: a packed pointer at an offset that isn't a
multiple of 8) could only travel as address bits, so instruction selection refuses to pass such a
composite by value.
-/

namespace Fir.AArch64

/-- What a register holds: 64 bits, or a pointer with its provenance (decision: AArch64
semantics). -/
inductive Word where
  | bits (b : BitVec 64)
  | ptr (p : Ptr)
  deriving DecidableEq, Repr, Inhabited

/-- How AAPCS64 passes a value of some type. -/
inductive PassKind where
  /-- An integer, bytes, or a pointer: one `x` register or 8-byte stack slot. -/
  | gp
  /-- A float: one FP register or 8-byte stack slot. -/
  | fp
  /-- An HFA of `n` floats of format `f`: `n` consecutive FP registers. -/
  | hfa (f : FloatTy) (n : Nat)
  /-- A composite of `n` 8-byte words (1 to 16 bytes); `even` if it is 16-byte aligned. -/
  | words (n : Nat) (even : Bool)
  /-- A composite larger than 16 bytes: a pointer to a copy. -/
  | ref
  /-- A composite of size 0: nothing. -/
  | none
  deriving DecidableEq, Repr

/-- A float format's size in bytes. -/
def _root_.Fir.FloatTy.bytes (f : FloatTy) : Nat := f.width / 8

mutual
  /-- Whether a type has a zero-length array anywhere in it, which keeps it from being an HFA
  (GCC's rule; an empty struct doesn't). -/
  def _root_.Fir.Ty.hasEmptyArray : Ty → Bool
    | .struct _ fs => Ty.hasEmptyArrayList fs
    | .array n e => n == 0 || e.hasEmptyArray
    | _ => false
  def _root_.Fir.Ty.hasEmptyArrayList : List Ty → Bool
    | [] => false
    | t :: ts => t.hasEmptyArray || Ty.hasEmptyArrayList ts
end

/-- The format and member count of an HFA: one to four leaves, floats of one format, that tile
the type in memory (one at each multiple of their size), which has no zero-length array. Memory
order, not the fields' declared order: AAPCS64 classifies the laid-out type, and a
`struct<auto>` or a nested packed struct can put a later field first. -/
def hfaOf? (sp : SpaceCfg) (t : Ty) : Option (FloatTy × Nat) :=
  match t.leaves sp with
  | ls@((_, .float f) :: _) =>
    let n := ls.length
    if n ≤ 4 && !t.hasEmptyArray && t.size sp == n * f.bytes &&
        ls.all (·.2 == .float f) && (List.range n).all (fun i => ls.any (·.1 == i * f.bytes)) then
      some (f, n)
    else none
  | _ => none

/-- How AAPCS64 passes a value of type `t`. -/
def passKind (sp : SpaceCfg) (t : Ty) : PassKind :=
  if t.isComposite then
    if t.size sp == 0 then .none
    else match hfaOf? sp t with
      | some (f, n) => .hfa f n
      | none => if t.size sp ≤ 16 then .words ((t.size sp + 7) / 8) (t.align sp ≥ 16) else .ref
  else if t.isFloat then .fp else .gp

/-- Whether a composite passed as `x` register words has a pointer leaf that doesn't fill one (at
an offset that isn't a multiple of 8). Registers could carry it only as shifted address bits,
which drops its provenance, so such a composite isn't passed by value (decision: C ABI for
aggregates; instruction selection refuses it, twin `abi::splits_ptr`). -/
def _root_.Fir.Ty.splitsPtr (sp : SpaceCfg) (t : Ty) : Bool :=
  (passKind sp t matches .words ..) && (t.leaves sp).any fun (o, l) => l == .ptr && o % 8 != 0

/-- Where an argument travels. -/
inductive ArgLoc where
  /-- A scalar in a register. -/
  | reg (r : Reg)
  /-- A scalar in the 8-byte stack slot this many bytes above `sp`. -/
  | stack (off : Nat)
  /-- A composite's pieces (`pieces`) in these registers. -/
  | regs (rs : List Reg)
  /-- A composite's bytes this many bytes above `sp`. -/
  | mem (off : Nat)
  /-- A pointer to a copy of the composite, in a register or the stack slot at an offset. -/
  | ref (l : Reg ⊕ Nat)
  /-- Nothing (an empty composite). -/
  | none
  deriving DecidableEq, Repr

/-- `n` consecutive registers of a class from `k`. -/
def regRun (mk : Nat → Reg) (k n : Nat) : List Reg := (List.range n).map fun i => mk (k + i)

/-- The locations of arguments of types `ts`, from NGRN `g`, NSRN `f`, and NSAA `s`, and the
NSAA after them. -/
def argLocsFrom (sp : SpaceCfg) : List Ty → Nat → Nat → Nat → List ArgLoc × Nat
  | [], _, _, s => ([], s)
  | t :: ts, g, f, s =>
    let (l, g, f, s) : ArgLoc × Nat × Nat × Nat := match passKind sp t with
      | .gp => if g < 8 then (.reg (.x g), g + 1, f, s) else (.stack s, g, f, s + 8)
      | .fp => if f < 8 then (.reg (.d f), g, f + 1, s) else (.stack s, g, f, s + 8)
      | .hfa fl n =>
        if f + n ≤ 8 then (.regs (regRun .d f n), g, f + n, s)
        else (.mem s, g, 8, s + alignUp (n * fl.bytes) 8)
      | .words n even =>
        let g := if even then alignUp g 2 else g
        if g + n ≤ 8 then (.regs (regRun .x g n), g + n, f, s)
        else
          let s := alignUp s (if even then 16 else 8)
          (.mem s, 8, f, s + 8 * n)
      | .ref => if g < 8 then (.ref (.inl (.x g)), g + 1, f, s) else (.ref (.inr s), g, f, s + 8)
      | .none => (.none, g, f, s)
    let (ls, s) := argLocsFrom sp ts g f s
    (l :: ls, s)

/-- Where AAPCS64 puts the arguments of a call with parameter types `ps` (decision: Calling
convention; variadic arguments go where fixed ones of their types would, decision: Varargs). -/
def argLocs (sp : SpaceCfg) (ps : List Ty) : List ArgLoc := (argLocsFrom sp ps 0 0 0).1

/-- How many bytes of stack the arguments take. -/
def argStack (sp : SpaceCfg) (ps : List Ty) : Nat := (argLocsFrom sp ps 0 0 0).2

/-- The registers a call's results come back in: for one composite, where it would be passed
first (its pieces' registers, none if it is empty); for scalars, `d0`, `d1` (`s0`, `s1`) when one
or two are floats of one format, otherwise `x0`, `x1`, a float as its bits. `none` when they come
back in memory at the address the caller passes in `x8`: a composite over 16 bytes (its bytes),
or three or more scalars (8-byte slots). -/
def resRegs (sp : SpaceCfg) (rets : List Ty) : Option (List Reg) :=
  match rets with
  | [t] =>
    if t.isComposite then
      match argLocs sp [t] with
      | [.regs rs] => some rs
      | [.none] => some []
      | _ => none
    else scalar
  | _ => scalar
where
  scalar : Option (List Reg) :=
    if rets.length > 2 then none
    else
      let fp := match rets with
        | .float f :: rest => rest.all (· == .float f)
        | _ => false
      some ((List.range rets.length).map fun i => if fp = true then .d i else .x i)

/-! ## Examples -/

private def s2 : Ty := .struct .c [.int 32, .int 32]
private def hfa3 : Ty := .struct .c [.float .f32, .array 2 (.float .f32)]
private def big : Ty := .struct .c [.int 64, .int 64, .int 8]
private def al16 : Ty := .struct .c [.array 0 (.int 128), .int 64]
private def sp0 : SpaceCfg := {}

#guard passKind sp0 s2 == .words 1 false
#guard passKind sp0 hfa3 == .hfa .f32 3
#guard passKind sp0 (.struct .c [.float .f32, .float .f64]) == .words 2 false
#guard passKind sp0 (.struct .packed [.float .f32, .float .f32]) == .hfa .f32 2
#guard passKind sp0 (.struct .c [.float .f32, .int 32]) == .words 1 false
#guard passKind sp0 big == .ref
#guard passKind sp0 al16 == .words 2 true
#guard passKind sp0 (.struct .c []) == .none
-- A zero-length array keeps a struct of floats from being an HFA; an empty struct doesn't.
#guard passKind sp0 (.struct .c [.array 0 (.float .f32), .float .f32]) == .words 1 false
#guard passKind sp0 (.struct .c [.float .f32, .struct .c [], .float .f32]) == .hfa .f32 2
-- Memory order: `auto` puts the `f32` (align 4) before the packed struct (align 1), so the
-- leaves in declared order are at offsets 4 and 0. It is an HFA, as C's `{float; P}` is.
#guard (Ty.struct .auto [.struct .packed [.float .f32], .float .f32]).leaves sp0 ==
  [(4, .float .f32), (0, .float .f32)]
#guard passKind sp0 (.struct .auto [.struct .packed [.float .f32], .float .f32]) == .hfa .f32 2
-- A packed pointer that straddles two words can't be passed by value; one at a word, or in a
-- composite passed by reference, can.
#guard (Ty.struct .packed [.int 8, .ptr]).splitsPtr sp0
#guard !(Ty.struct .c [.int 8, .ptr]).splitsPtr sp0
#guard !(Ty.struct .packed [.int 8, .ptr, .int 64, .int 64]).splitsPtr sp0
#guard argLocs sp0 [.int 32, .float .f64, .ptr] == [.reg (.x 0), .reg (.d 0), .reg (.x 1)]
#guard (argLocs sp0 ((List.replicate 9 (.float .f32)) ++ [.int 8])).getLast? == some (.reg (.x 0))
#guard argStack sp0 ((List.replicate 9 (.float .f32)) ++ (List.replicate 10 (.int 8))) == 24
-- Seven `x` registers taken: a two-word struct goes on the stack, and so does everything after.
#guard argLocs sp0 ((List.replicate 7 .ptr) ++ [.struct .c [.int 64, .int 64], .int 8]) ==
  (List.range 7).map (fun i => .reg (.x i)) ++ [.mem 0, .stack 16]
-- A 16-byte aligned struct starts at an even register.
#guard argLocs sp0 [.int 8, al16, .int 8] == [.reg (.x 0), .regs [.x 2, .x 3], .reg (.x 4)]
-- An HFA that doesn't fit the FP registers left goes on the stack, and so does every float after.
#guard argLocs sp0 ((List.replicate 6 (.float .f64)) ++ [hfa3, .float .f32]) ==
  (List.range 6).map (fun i => .reg (.d i)) ++ [.mem 0, .stack 16]
#guard argLocs sp0 [big, big] == [.ref (.inl (.x 0)), .ref (.inl (.x 1))]
#guard resRegs sp0 [hfa3] == some [.d 0, .d 1, .d 2]
#guard resRegs sp0 [s2] == some [.x 0]
#guard resRegs sp0 [big] == none
#guard resRegs sp0 [.float .f32, .float .f32] == some [.d 0, .d 1]
#guard resRegs sp0 [.float .f32, .float .f64] == some [.x 0, .x 1]
#guard resRegs sp0 [.int 8, .float .f64] == some [.x 0, .x 1]

/-! ## Bytes in registers -/

/-- A composite value's bytes: its leaves' encodings at their offsets, `poison` in the padding. -/
def compositeBytes (sp : SpaceCfg) (t : Ty) (leaves : List (Nat × List Byte)) : List Byte :=
  readBytes (leaves.foldl (fun m (o, bs) => writeBytes m o bs) ∅) 0 (t.size sp)

/-- `n` chunks of `w` bytes from the front of `bs` (the last ones shorter, or empty, past its end). -/
def chunks (w : Nat) : Nat → List Byte → List (List Byte)
  | 0, _ => []
  | n + 1, bs => bs.take w :: chunks w n (bs.drop w)

/-- The bytes each register gets of a composite passed in registers: 8-byte words (the last one
shorter), or an HFA's members. -/
def pieces (k : PassKind) (bs : List Byte) : List (List Byte) :=
  match k with
  | .words n _ => chunks 8 n bs
  | .hfa f n => chunks f.bytes n bs
  | _ => []

/-- Chunks that reach the end of the bytes, joined, are the bytes. -/
theorem chunks_flatten (w : Nat) : ∀ (n : Nat) (bs : List Byte), bs.length ≤ w * n →
    (chunks w n bs).flatten = bs
  | 0, bs, h => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    simp [this, chunks]
  | n + 1, bs, h => by
    simp only [chunks, List.flatten_cons]
    rw [chunks_flatten w n (bs.drop w) (by simp; rw [Nat.mul_succ] at h; omega), List.take_append_drop]

theorem length_chunk_le (w : Nat) : ∀ (n : Nat) (bs : List Byte), ∀ pc ∈ chunks w n bs, pc.length ≤ w
  | 0, _ => by simp [chunks]
  | n + 1, bs => by
    intro pc hpc
    simp only [chunks, List.mem_cons] at hpc
    rcases hpc with rfl | hpc
    · simp only [List.length_take]; omega
    · exact length_chunk_le w n _ pc hpc

/-- **A composite's pieces, joined, are its bytes**: the registers of a composite passed in
registers hold its bytes, in order, and nothing else. -/
theorem pieces_flatten {sp : SpaceCfg} {t : Ty} {bs : List Byte} (hl : bs.length = t.size sp)
    (hk : (∃ n e, passKind sp t = .words n e) ∨ (∃ f n, passKind sp t = .hfa f n)) :
    (pieces (passKind sp t) bs).flatten = bs := by
  rcases hk with ⟨n, e, he⟩ | ⟨f, n, he⟩ <;> rw [he] <;> simp only [pieces] <;>
    apply chunks_flatten <;> rw [hl] <;> revert he <;> unfold passKind <;>
    split <;> (try split) <;> (try split) <;> (try split) <;> intro he <;> (try cases he)
  · omega
  · rename_i heq
    unfold hfaOf? at heq
    split at heq
    · simp only at heq
      split at heq
      · rename_i hc
        cases heq
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        rw [hc.1.1.2, Nat.mul_comm]
        exact Nat.le_refl _
      · cases heq
    · cases heq

/-- Whether a byte is defined bits. -/
def Byte.isBits : Byte → Bool
  | .bits _ => true
  | _ => false

/-- The bits of a defined byte. -/
def Byte.val : Byte → Nat
  | .bits b => b.toNat
  | _ => 0

/-- The word a register holds once these bytes (eight at most) are loaded into it as `ldr`
loads them: a pointer if they are its eight fragments in order, otherwise their bits, if every
byte is defined. -/
def Word.ofBytes? (bs : List Byte) : Option Word :=
  match ptrOfFrags? 8 bs with
  | some p => some (.ptr p)
  | none => if bs.all Byte.isBits then some (.bits (BitVec.ofNat 64 (undigits (bs.map Byte.val))))
    else none

/-- A register's low `n` bytes, as `str` stores them: a pointer's eight fragments, or bits. -/
def Word.bytes (n : Nat) : Word → List Byte
  | .ptr p => (List.range 8).map (.frag p)
  | .bits b => (digits n b.toNat).map fun d => .bits (BitVec.ofNat 8 d)

theorem digits_undigits : ∀ ds : List Nat, (∀ d ∈ ds, d < 256) →
    digits ds.length (undigits ds) = ds
  | [], _ => rfl
  | d :: ds, h => by
    have hd := h d (by simp)
    simp only [List.length_cons, digits, undigits]
    have h1 : (d + 256 * undigits ds) % 256 = d := by omega
    have h2 : (d + 256 * undigits ds) / 256 = undigits ds := by omega
    rw [h1, h2, digits_undigits ds (fun x hx => h x (by simp [hx]))]

theorem undigits_lt : ∀ ds : List Nat, (∀ d ∈ ds, d < 256) → undigits ds < 256 ^ ds.length
  | [], _ => by simp [undigits]
  | d :: ds, h => by
    have hd := h d (by simp)
    have := undigits_lt ds (fun x hx => h x (by simp [hx]))
    simp only [undigits, List.length_cons, Nat.pow_succ]
    omega

/-- **A defined piece put in a register and read back is the piece**: its bits, or the pointer
its fragments make, provenance included. -/
theorem Word.bytes_ofBytes {bs : List Byte} {w : Word} (h : Word.ofBytes? bs = some w)
    (hn : bs.length ≤ 8) : w.bytes bs.length = bs := by
  unfold Word.ofBytes? at h
  split at h
  · rename_i p hp
    cases h
    unfold ptrOfFrags? at hp
    split at hp
    · rename_i rest
      split at hp
      · rename_i heq
        cases hp
        have := (beq_iff_eq.mp heq)
        rw [this]
        simp [Word.bytes]
      · cases hp
    · cases hp
  · split at h
    · rename_i hall
      cases h
      have hlt : ∀ d ∈ bs.map Byte.val, d < 256 := by
        intro d hd
        simp only [List.mem_map] at hd
        obtain ⟨b, _, rfl⟩ := hd
        cases b <;> simp [Byte.val]
        exact BitVec.isLt _
      have hu := undigits_lt _ hlt
      have h64 : undigits (bs.map Byte.val) < 2 ^ 64 := by
        have : (256 : Nat) ^ (bs.map Byte.val).length ≤ 256 ^ 8 :=
          Nat.pow_le_pow_right (by decide) (by simpa using hn)
        have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
        omega
      simp only [Word.bytes, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64]
      have := digits_undigits _ hlt
      rw [List.length_map] at this
      rw [this, List.map_map]
      conv => rhs; rw [← List.map_id bs]
      apply List.map_congr_left
      intro b hb
      have := List.all_eq_true.mp hall b hb
      cases b <;> simp_all [Byte.isBits, Byte.val]
    · cases h

/-- **Registers carry a composite's defined bytes exactly**: split into its pieces, each loaded
into a register and stored back, a composite's bytes come back unchanged when every piece is
defined (no `poison`, and no pointer fragment outside a whole pointer). -/
theorem roundTrip {sp : SpaceCfg} {t : Ty} {bs : List Byte} (hl : bs.length = t.size sp)
    (hk : (∃ n e, passKind sp t = .words n e) ∨ (∃ f n, passKind sp t = .hfa f n))
    (hdef : ∀ pc ∈ pieces (passKind sp t) bs, (Word.ofBytes? pc).isSome) :
    ((pieces (passKind sp t) bs).map fun pc =>
      ((Word.ofBytes? pc).map (·.bytes pc.length)).getD []).flatten = bs := by
  conv => rhs; rw [← pieces_flatten hl hk]
  congr 1
  conv => rhs; rw [← List.map_id (pieces (passKind sp t) bs)]
  apply List.map_congr_left
  intro pc hpc
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hdef pc hpc)
  have hlen : pc.length ≤ 8 := by
    rcases hk with ⟨n, e, he⟩ | ⟨f, n, he⟩ <;> rw [he] at hpc <;> simp only [pieces] at hpc
    · exact length_chunk_le 8 n bs pc hpc
    · have := length_chunk_le f.bytes n bs pc hpc
      have h8 : f.bytes ≤ 8 := by cases f <;> decide
      omega
  simp [hw, Word.bytes_ofBytes hw hlen]


/-! ## Partly defined pieces

`roundTrip` needs every piece defined. A composite's pieces usually aren't: padding is `poison`,
and a `poison` leaf is too. What a register gets for such a piece is the machine's choice
(`wordOfBytes` in `Fir.AArch64Machine`: an oracle byte for `poison`, a fragment's address byte
for a fragment of no whole pointer). `Word.Holds` says what any such choice keeps: the pointer
of a piece of eight fragments of one pointer, else bits that agree with every defined byte. -/

/-- What a register may hold for a piece: the pointer whose eight fragments it is, or, for any
other piece, bits whose low bytes are the piece's defined ones (any bits where it is `poison` or
a fragment). -/
def Word.Holds (pc : List Byte) : Word → Prop
  | .ptr p => ptrOfFrags? 8 pc = some p
  | .bits b => ptrOfFrags? 8 pc = none ∧
      ∀ (i : Nat) (x : BitVec 8), pc[i]? = some (Byte.bits x) →
        ((Word.bits b).bytes pc.length)[i]? = some (Byte.bits x)

/-- Bytes that arrived for `sent`: as many, and each defined byte of `sent` in place. -/
def Agrees (got sent : List Byte) : Prop :=
  got.length = sent.length ∧
    ∀ (i : Nat) (x : BitVec 8), sent[i]? = some (Byte.bits x) → got[i]? = some (Byte.bits x)

theorem Agrees.append {a b c d : List Byte} (h1 : Agrees a b) (h2 : Agrees c d) :
    Agrees (a ++ c) (b ++ d) := by
  refine ⟨by simp [h1.1, h2.1], fun i x hx => ?_⟩
  rcases Nat.lt_or_ge i b.length with h | h
  · rw [List.getElem?_append_left h] at hx
    rw [List.getElem?_append_left (h1.1 ▸ h)]
    exact h1.2 i x hx
  · rw [List.getElem?_append_right h] at hx
    rw [List.getElem?_append_right (h1.1 ▸ h), h1.1]
    exact h2.2 _ x hx

/-- The word the machine puts in a register for a piece (`wordOfBytes`), given what it picks for
the bytes that aren't bits (`c i` for byte `i`): the pointer of eight fragments of one, else the
bits, little-endian. -/
def Word.fill (c : Nat → Nat) (pc : List Byte) : Word :=
  match ptrOfFrags? 8 pc with
  | some p => .ptr p
  | none => .bits (BitVec.ofNat 64 (undigits (pc.zipIdx.map fun (b, i) =>
      match b with
      | .bits x => x.toNat
      | _ => c i % 256)))

theorem frags_ptrOfFrags (p : Ptr) : ptrOfFrags? 8 ((List.range 8).map (.frag p)) = some p := by
  simp [ptrOfFrags?, List.range_succ]

theorem eq_frags_of_ptrOfFrags {pc : List Byte} {p : Ptr} (h : ptrOfFrags? 8 pc = some p) :
    pc = (List.range 8).map (.frag p) := by
  unfold ptrOfFrags? at h
  split at h
  · split at h
    · rename_i heq
      cases h
      exact beq_iff_eq.mp heq
    · cases h
  · cases h

theorem length_digits : ∀ (k n : Nat), (digits k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [digits, length_digits k]

/-- **The machine's word for a piece holds it**: whatever it picks for `poison` and stray
fragments, a word of eight fragments of one pointer is that pointer, and every defined byte is
in the register. -/
theorem Word.holds_fill (c : Nat → Nat) {pc : List Byte} (hn : pc.length ≤ 8) :
    (Word.fill c pc).Holds pc := by
  unfold Word.fill
  split
  · rename_i p hp
    exact hp
  · rename_i hp
    refine ⟨hp, ?_⟩
    intro i x hi
    let ds := pc.zipIdx.map fun (b, i) =>
      match b with
      | .bits x => x.toNat
      | _ => c i % 256
    have hlt : ∀ d ∈ ds, d < 256 := by
      intro d hd
      simp only [ds, List.mem_map] at hd
      obtain ⟨⟨b, j⟩, _, rfl⟩ := hd
      cases b <;> simp <;> first | exact BitVec.isLt _ | exact Nat.mod_lt _ (by decide)
    have hlen : ds.length = pc.length := by simp [ds]
    have h64 : undigits ds < 2 ^ 64 := by
      have := undigits_lt ds hlt
      have : (256 : Nat) ^ ds.length ≤ 256 ^ 8 :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have : (256 : Nat) ^ 8 = 2 ^ 64 := by decide
      omega
    have hd := digits_undigits ds hlt
    rw [hlen] at hd
    show ((Word.bits (BitVec.ofNat 64 (undigits ds))).bytes pc.length)[i]? = _
    simp only [Word.bytes, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt h64, hd]
    have hi' : i < pc.length := by
      rcases Nat.lt_or_ge i pc.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hi; cases hi
    have hpi : pc[i] = .bits x := by
      rw [List.getElem?_eq_getElem hi'] at hi; exact Option.some.inj hi
    simp [ds, List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi', hpi]

/-- A register that holds a piece gives back, stored, bytes that agree with it, and the piece
itself if it is a whole pointer. -/
theorem Word.holds_bytes {pc : List Byte} {w : Word} (h : w.Holds pc) :
    Agrees (w.bytes pc.length) pc := by
  cases w with
  | ptr p =>
    have := eq_frags_of_ptrOfFrags (show ptrOfFrags? 8 pc = some p from h)
    subst this
    have hb : (Word.ptr p).bytes ((List.range 8).map (Byte.frag p)).length =
        (List.range 8).map (.frag p) := rfl
    rw [hb]
    exact ⟨rfl, fun _ _ h => h⟩
  | bits b =>
    refine ⟨?_, h.2⟩
    simp only [Word.bytes, List.length_map]
    exact length_digits _ _

/-- The `k`th of `n` chunks of `w` bytes is the `w` bytes from `w * k`. -/
theorem chunks_getElem? (w : Nat) : ∀ (n k : Nat) (bs : List Byte), k < n →
    (chunks w n bs)[k]? = some ((bs.drop (w * k)).take w)
  | 0, _, _, h => by omega
  | n + 1, 0, bs, _ => by simp [chunks]
  | n + 1, k + 1, bs, h => by
    simp only [chunks, List.getElem?_cons_succ]
    rw [chunks_getElem? w n k (bs.drop w) (by omega), List.drop_drop, Nat.mul_succ, Nat.add_comm]

/-- Words for pieces: one each, each holding its piece. -/
def Word.HoldAll (pcs : List (List Byte)) (ws : List Word) : Prop :=
  ws.length = pcs.length ∧
    ∀ (i : Nat) (pc : List Byte) (w : Word), pcs[i]? = some pc → ws[i]? = some w → w.Holds pc

/-- **Registers carry a composite's defined bytes, padding or not**: whatever words hold its
pieces (`Word.Holds`, as the machine's do: `Word.holds_fill`), stored back they give as many
bytes as it has, with every defined byte of it in place, whatever its padding and `poison`
leaves held. -/
theorem arrives {sp : SpaceCfg} {t : Ty} {bs : List Byte} (hl : bs.length = t.size sp)
    (hk : (∃ n e, passKind sp t = .words n e) ∨ (∃ f n, passKind sp t = .hfa f n))
    {ws : List Word} (hw : Word.HoldAll (pieces (passKind sp t) bs) ws) :
    Agrees (List.zipWith (fun pc (w : Word) => w.bytes pc.length) (pieces (passKind sp t) bs) ws).flatten
      bs := by
  conv => rhs; rw [← pieces_flatten hl hk]
  generalize pieces (passKind sp t) bs = pcs at hw
  induction pcs generalizing ws with
  | nil =>
    have : ws = [] := List.eq_nil_of_length_eq_zero hw.1
    subst this
    exact ⟨rfl, fun _ _ h => by simp at h⟩
  | cons pc pcs ih =>
    cases ws with
    | nil => exact absurd hw.1 (by simp)
    | cons w ws =>
      simp only [List.zipWith_cons_cons, List.flatten_cons]
      have h0 : w.Holds pc := hw.2 0 pc w rfl rfl
      have hr : Word.HoldAll pcs ws :=
        ⟨by simpa using hw.1, fun i q v hq hv => hw.2 (i + 1) q v (by simpa using hq) (by simpa using hv)⟩
      exact (Word.holds_bytes h0).append (ih hr)

/-- **A pointer leaf keeps its provenance**: in a composite passed as words that doesn't split a
pointer (`Ty.splitsPtr`, which instruction selection refuses), a pointer leaf at offset `o` whose
bytes are its eight fragments is in register `o / 8` as that pointer, whatever the other pieces
hold, and so is stored back as those fragments (`Word.holds_bytes`). -/
theorem ptrLeaf_inReg {sp : SpaceCfg} {t : Ty} {bs : List Byte} {n : Nat} {e : Bool}
    (hk : passKind sp t = .words n e) (hs : t.splitsPtr sp = false) (hl : bs.length = t.size sp)
    {o : Nat} (ho : (o, Ty.ptr) ∈ t.leaves sp) {p : Ptr}
    (hb : (bs.drop o).take 8 = (List.range 8).map (.frag p))
    {ws : List Word} (hw : Word.HoldAll (pieces (passKind sp t) bs) ws) :
    ws[o / 8]? = some (.ptr p) := by
  have h8 : o % 8 = 0 := by
    unfold Ty.splitsPtr at hs
    rw [hk] at hs
    simp only [Bool.true_and, List.any_eq_false] at hs
    have := hs _ ho
    simp at this
    exact this
  have hn : n = (t.size sp + 7) / 8 := by
    revert hk; unfold passKind
    split <;> (try split) <;> (try split) <;> (try split) <;> intro hk <;> cases hk <;> rfl
  have hfit : o + 8 ≤ bs.length := by
    have := congrArg List.length hb
    simp only [List.length_take, List.length_drop, List.length_map, List.length_range] at this
    omega
  have hk8 : o / 8 < n := by omega
  have hpc : (pieces (passKind sp t) bs)[o / 8]? = some ((List.range 8).map (.frag p)) := by
    rw [hk]; simp only [pieces]
    rw [chunks_getElem? 8 n (o / 8) bs hk8, ← hb]
    congr 3; omega
  have hlt : o / 8 < ws.length := by
    rw [hw.1]
    rcases Nat.lt_or_ge (o / 8) (pieces (passKind sp t) bs).length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hpc; cases hpc
  have hh := hw.2 (o / 8) _ ws[o / 8] hpc (List.getElem?_eq_getElem hlt)
  rw [List.getElem?_eq_getElem hlt]
  revert hh
  cases ws[o / 8] with
  | ptr q =>
    intro hh
    have := (show ptrOfFrags? 8 _ = some q from hh)
    rw [frags_ptrOfFrags] at this
    rw [Option.some.inj this]
  | bits b =>
    intro hh
    have := hh.1
    rw [frags_ptrOfFrags] at this
    cases this

end Fir.AArch64
