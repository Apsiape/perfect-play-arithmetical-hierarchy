import Sigma2.CompilerEffectiveRowCoefficients
import Sigma2.CompilerEffectiveBits
noncomputable section
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective
set_option allowUnsafeReducibility true in
attribute [local reducible] CompilerScaffold.rows
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList
  integerAt rationalAt rowAt nameAt
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.cond Computable.option_some
variable {α β : Type} [Primcodable α] [Primcodable β]

abbrev SlotData := Option ℕ × Bool

def slotView {n : ℕ} (s : RowSlots.Slot n) : SlotData := (s.event.map Fin.val,s.negative)

@[fun_prop] theorem creplicate (n : α → ℕ) (f : α → β) (hn : Computable n) (hf : Computable f) :
    Computable (fun a => List.replicate (n a) (f a)) := by
  have hc := cmap (fun a => List.range (n a)) (fun z => f z.1) (crange _ hn) (hf.comp Computable.fst)
  exact hc.of_eq (fun a => by simp)
@[fun_prop] theorem cflatten (f : α → List (List β)) (hf : Computable f) :
    Computable (fun a => (f a).flatten) := Primrec.list_flatten.to_comp.comp hf
@[fun_prop] theorem cintegerAt (P : α → Presentation) (r i : α → ℕ)
    (hP : Computable P) (hr : Computable r) (hi : Computable i) :
    Computable (fun a => integerAt (P a) (r a) (i a)) := integerAt_computable.comp (hP.pair (hr.pair hi))

def termNat (e : Option ℕ) (c : ℤ) : List SlotData :=
  (List.replicate c.natAbs [(none,decide (c<0)),(e,decide (c<0))]).flatten

def rawNat (P : Presentation) (r : ℕ) : List SlotData :=
  [(none,false),(none,true)] ++ termNat none (integerAt P r 0) ++
    (List.range (names P).length).flatMap (fun i => termNat (some i) (integerAt P r (i+1)))

def boundNat (P : Presentation) : ℕ :=
  ((List.range (rowList P).length).map (fun r => (rawNat P r).length)).sum+1

def squaresNat (P : Presentation) : ℕ := Nat.log 4 (boundNat P)+1

def dimensionNat (P : Presentation) : ℕ := 4^squaresNat P

def slotsNat (P : Presentation) (r : ℕ) : List SlotData :=
  rawNat P r ++ (List.replicate ((dimensionNat P-(rawNat P r).length)/2)
    [(none,false),(none,true)]).flatten

def slotNat (P : Presentation) (r j : ℕ) : SlotData :=
  (slotsNat P r)[j]?.getD (none,false)
attribute [local irreducible] termNat rawNat boundNat squaresNat dimensionNat slotsNat slotNat

@[fun_prop] theorem ctermNat (e : α → Option ℕ) (c : α → ℤ)
    (he : Computable e) (hc : Computable c) :
    Computable (fun a => termNat (e a) (c a)) := by unfold termNat; fun_prop
@[fun_prop] theorem crawNat (P : α → Presentation) (r : α → ℕ)
    (hP : Computable P) (hr : Computable r) :
    Computable (fun a => rawNat (P a) (r a)) := by unfold rawNat; fun_prop
@[fun_prop] theorem cboundNat (P : α → Presentation) (hP : Computable P) :
    Computable (fun a => boundNat (P a)) := by unfold boundNat; fun_prop
@[fun_prop] theorem csquaresNat (P : α → Presentation) (hP : Computable P) :
    Computable (fun a => squaresNat (P a)) := by unfold squaresNat; fun_prop
@[fun_prop] theorem cdimensionNat (P : α → Presentation) (hP : Computable P) :
    Computable (fun a => dimensionNat (P a)) := by unfold dimensionNat; fun_prop
@[fun_prop] theorem cslotsNat (P : α → Presentation) (r : α → ℕ)
    (hP : Computable P) (hr : Computable r) :
    Computable (fun a => slotsNat (P a) (r a)) := by unfold slotsNat; fun_prop
@[fun_prop] theorem cslotNat (P : α → Presentation) (r j : α → ℕ)
    (hP : Computable P) (hr : Computable r) (hj : Computable j) :
    Computable (fun a => slotNat (P a) (r a) (j a)) := by unfold slotNat; fun_prop

theorem termNat_eq {n : ℕ} (e : Option (Fin n)) (c : ℤ) :
    termNat (e.map Fin.val) c=(RowSlots.term e c).map slotView := by
  simp [termNat,RowSlots.term,List.map_flatten,List.map_replicate,slotView]

theorem integerAt_c_eq (P : Presentation) (r : Fin (rowList P).length) (i : Fin ((names P).length+1)) :
    integerAt P r.val i.val=RowSlots.c (rows P) r i := integerAt_eq P r i

theorem flatten_map_eq {σ τ : Type} (xs : List σ) (f : σ → List τ) :
    (xs.map f).flatten=xs.flatMap f := by induction xs <;> simp_all

theorem rawNat_eq (P : Presentation) (r : Fin (rowList P).length) :
    rawNat P r.val=(RowSlots.raw (rows P) r).map slotView := by
  have hl := ofFn_eq_range
    (fun i : Fin (names P).length => termNat (some i.val) (RowSlots.c (rows P) r i.succ))
    (fun i => termNat (some i) (integerAt P r.val (i+1))) (by
      intro i
      rw [← integerAt_c_eq]
      rfl)
  simp only [rawNat,RowSlots.raw,List.map_append,List.map_cons,List.map_nil,List.map_flatten,
    List.map_ofFn,Function.comp_def,← termNat_eq,slotView,Option.map_none,Option.map_some]
  rw [hl,flatten_map_eq,← integerAt_c_eq]
  simp only [Fin.val_zero]

@[simp] theorem slotView_length {n : ℕ} (l : List (RowSlots.Slot n)) : (l.map slotView).length=l.length := by simp only [List.length_map]

theorem boundNat_eq (P : Presentation) : boundNat P=RowSlots.bound (rows P) := by
  have hl := ofFn_eq_range (fun r : Fin (rowList P).length => (RowSlots.raw (rows P) r).length)
    (fun r => (rawNat P r).length) (fun r => by rw [rawNat_eq,List.length_map])
  unfold boundNat RowSlots.bound
  rw [hl]

theorem squaresNat_eq (P : Presentation) : squaresNat P=RowSlots.squares (rows P) := by
  unfold squaresNat RowSlots.squares
  rw [boundNat_eq]

theorem dimensionNat_eq (P : Presentation) : dimensionNat P=RowSlots.dimension (rows P) := by
  unfold dimensionNat RowSlots.dimension
  rw [squaresNat_eq]

theorem slotsNat_eq (P : Presentation) (r : Fin (rowList P).length) :
    slotsNat P r.val=(RowSlots.slots (rows P) r).map slotView := by
  simp [slotsNat,RowSlots.slots,rawNat_eq,dimensionNat_eq,List.map_append,List.map_flatten,
    List.map_replicate,slotView]

theorem slotNat_eq (P : Presentation) (r : Fin (rowList P).length) (j : ℕ) :
    slotNat P r.val j=slotView (RowSlots.slot (rows P) r j) := by
  unfold slotNat RowSlots.slot
  rw [slotsNat_eq]
  cases h : (RowSlots.slots (rows P) r)[j]? <;> simp [h,slotView]

#print axioms crawNat
#print axioms cboundNat
#print axioms cdimensionNat
#print axioms cslotNat
#print axioms rawNat_eq
#print axioms slotsNat_eq
#print axioms slotNat_eq
end Sigma2.CompilerEffectiveCoding