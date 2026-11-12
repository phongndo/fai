import Fir.Syntax

/-!
# Data layout

Where each part of a struct or array goes in memory, from the memory space's data layout
(decisions: Layout, Data layout). Sizes and alignments are in bytes.

* `iN` and `bN` take `N / 8` bytes and the alignment the space lists for their width; a pointer
  takes the space's pointer size and alignment. A float takes its bits and aligns like the
  integer of its width (decision: Floats).
* A field or element takes its *stride*: its size rounded up to its alignment.
* `struct<C>` places each field at the next multiple of its alignment, in order. The struct's
  alignment is its largest field's (1 if it has none), and its size is where the last field ends,
  rounded up to that alignment.
* `struct<packed>` places the fields one after another, with alignment 1.
* `struct<auto>` places the fields by the C rule after a stable sort by decreasing alignment.
  FIR may change this rule, so programs must not rely on it beyond what `ptr.field` and
  `ty.offset` report.
* `array<N x T>` is `N` strides of `T`, with `T`'s alignment.

* `slice` is laid out as `struct<C>{ptr, iA}`, with `A` the address size.

Function types and unions have no layout; the verifier keeps them out of memory.
-/

namespace Fir

def alignUp (x a : Nat) : Nat := if a ≤ 1 then x else (x + a - 1) / a * a

/-- Place fields, given as `(index, stride, alignment)`, in this order by the C rule: each field's
offset, by index, and where the last one ends. -/
def placeC (fs : List (Nat × Nat × Nat)) : List (Nat × Nat) × Nat :=
  fs.foldl (init := ([], 0)) fun (acc, o) (i, s, a) =>
    let o := alignUp o a
    (acc ++ [(i, o)], o + s)

/-- A struct's layout from its fields' strides and alignments: each field's offset, in declared
order, the size, and the alignment. -/
def placeFields (p : Policy) (ds : List (Nat × Nat)) : List Nat × Nat × Nat :=
  let fs := ds.zipIdx.map fun ((s, a), i) => (i, s, a)
  let align := ds.foldl (fun m (_, a) => max m a) 1
  match p with
  | .packed =>
    let (offs, size) := placeC (fs.map fun (i, s, _) => (i, s, 1))
    (offs.map (·.2), size, 1)
  | .c =>
    let (offs, size) := placeC fs
    (offs.map (·.2), alignUp size align, align)
  | .auto =>
    let (offs, size) := placeC (fs.mergeSort fun x y => x.2.2 ≥ y.2.2)
    ((List.range ds.length).map fun i => ((offs.find? (·.1 == i)).map (·.2)).getD 0,
      alignUp size align, align)

/-- The size and alignment of `iN` and `bN`. -/
def SpaceCfg.intDims (sp : SpaceCfg) (w : Nat) : Nat × Nat := (w / 8, sp.intAlign w)

/-- A slice's layout, as `struct<C>{ptr, iA}`: the length's offset, the size, and the alignment. -/
def SpaceCfg.sliceLayout (sp : SpaceCfg) : Nat × Nat × Nat :=
  let (ls, la) := sp.intDims sp.addrBits
  match placeFields .c [(alignUp (sp.ptrBits / 8) sp.ptrAlign, sp.ptrAlign), (alignUp ls la, la)] with
  | (offs, size, align) => (offs.getD 1 0, size, align)

mutual
  /-- A type's size and alignment. -/
  def Ty.dims (sp : SpaceCfg) : Ty → Nat × Nat
    | .int w | .byte w => (w / 8, sp.intAlign w)
    | .float f => (f.width / 8, sp.intAlign f.width)
    | .ptr => (sp.ptrBits / 8, sp.ptrAlign)
    | .struct p fs => let (_, size, align) := placeFields p (Ty.strides sp fs); (size, align)
    | .array n t => let (s, a) := t.dims sp; (n * alignUp s a, a)
    | .func .. | .union _ => (0, 1)
    | .slice => (sp.sliceLayout.2.1, sp.sliceLayout.2.2)
  /-- Each type's stride and alignment. -/
  def Ty.strides (sp : SpaceCfg) : List Ty → List (Nat × Nat)
    | [] => []
    | t :: ts => let (s, a) := t.dims sp; (alignUp s a, a) :: Ty.strides sp ts
end

/-- How many bytes a value of type `t` takes in memory. -/
def Ty.size (sp : SpaceCfg) : Ty → Nat
  | .int w | .byte w => w / 8
  | .float f => f.width / 8
  | .ptr => sp.ptrBits / 8
  | t => (t.dims sp).1

def Ty.align (sp : SpaceCfg) (t : Ty) : Nat := (t.dims sp).2

/-- How far apart array elements of type `t` are. -/
def Ty.stride (sp : SpaceCfg) (t : Ty) : Nat := alignUp (t.dims sp).1 (t.dims sp).2

/-- The offset of field `i` of a struct. -/
def Ty.fieldOffset? (sp : SpaceCfg) : Ty → Nat → Option Nat
  | .struct p fs, i => (placeFields p (Ty.strides sp fs)).1[i]?
  | _, _ => none

/-- Whether values of the type can be part of memory: everything but function types, unions, and
integers whose size isn't whole bytes. (The verifier checks the parts of structs and arrays.) -/
def Ty.hasLayout : Ty → Bool
  | .int w => w % 8 == 0
  | .func .. | .union _ => false
  | _ => true

mutual
  /-- The scalars a value of type `t` is stored as, in order (fields and elements depth first),
  with their offsets: an aggregate load or store accesses exactly these (decision: Aggregate
  values). A scalar is its own only leaf; types without a layout have none that matter. -/
  def Ty.leaves (sp : SpaceCfg) : Ty → List (Nat × Ty)
    | .struct p fs => Ty.leavesAt sp (placeFields p (Ty.strides sp fs)).1 fs
    | .array n e =>
      let ls := e.leaves sp
      (List.range n).flatMap fun j => ls.map fun (o, t) => (j * e.stride sp + o, t)
    | .slice => [(0, .ptr), (sp.sliceLayout.1, .int sp.addrBits)]
    | t => [(0, t)]
  /-- The leaves of fields at these offsets. -/
  def Ty.leavesAt (sp : SpaceCfg) : List Nat → List Ty → List (Nat × Ty)
    | o :: os, f :: fs => (f.leaves sp).map (fun (x, t) => (o + x, t)) ++ Ty.leavesAt sp os fs
    | _, _ => []
end

end Fir
