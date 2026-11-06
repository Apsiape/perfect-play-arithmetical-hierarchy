import Sigma2.CompilerHonestLabels
import Sigma2.CompilerScaffold

/-! Simultaneous allocation of all label encoding slots, with the exact
one-slot/two-slot widths and offsets of the frozen compiler. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerHonestAllocation
open Compiler CompilerScaffold CompilerHonestLabels

def width (t : LabelType) : ℕ := if t=.contraction then 2 else 1

def offset (ts : List LabelType) (i : ℕ) : ℕ := ((ts.take i).map width).sum

def pack : List LabelType → (ℕ → Op) → (ℕ → Op) → List Op
  | [],_,_ => []
  | t::ts,U,V => U 0 ::
      (if t=.contraction then V 0 :: pack ts (fun i => U (i+1)) (fun i => V (i+1))
       else pack ts (fun i => U (i+1)) (fun i => V (i+1)))

theorem pack_length (ts : List LabelType) (U V : ℕ → Op) :
    (pack ts U V).length=(ts.map width).sum := by
  induction ts generalizing U V with
  | nil => rfl
  | cons t ts ih =>
      cases t <;> simp [pack,width,ih] <;> omega

theorem pack_first (ts : List LabelType) (U V : ℕ → Op) (i : ℕ)
    (hi : i<ts.length) : (pack ts U V)[offset ts i]?=some (U i) := by
  induction ts generalizing U V i with
  | nil => simp at hi
  | cons t ts ih =>
      cases i with
      | zero => simp [offset,pack]
      | succ i =>
          have hi' : i<ts.length := by simpa using hi
          have hh := ih (fun j => U (j+1)) (fun j => V (j+1)) i hi'
          cases t <;> simpa [pack,offset,width,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

theorem pack_second (ts : List LabelType) (U V : ℕ → Op) (i : ℕ)
    (hi : ts[i]?=some .contraction) :
    (pack ts U V)[offset ts i+1]?=some (V i) := by
  induction ts generalizing U V i with
  | nil => simp at hi
  | cons t ts ih =>
      cases i with
      | zero =>
          have ht : t=.contraction := by simpa using hi
          subst t
          simp [offset,pack]
      | succ i =>
          have hi' : ts[i]?=some .contraction := by simpa using hi
          have hh := ih (fun j => U (j+1)) (fun j => V (j+1)) i hi'
          cases t <;> simpa [pack,offset,width,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

theorem pack_property (ts : List LabelType) (U V : ℕ → Op) (p : Op → Prop)
    (hU : ∀ i,p (U i)) (hV : ∀ i,p (V i)) : ∀ A ∈ pack ts U V,p A := by
  induction ts generalizing U V with
  | nil => simp [pack]
  | cons t ts ih =>
      intro A hA
      simp only [pack,List.mem_cons] at hA
      rcases hA with hA|hA
      · subst A; exact hU 0
      · split_ifs at hA with ht
        · rcases List.mem_cons.mp hA with hA|hA
          · subst A; exact hV 0
          · exact ih _ _ (fun i => hU (i+1)) (fun i => hV (i+1)) A hA
        · exact ih _ _ (fun i => hU (i+1)) (fun i => hV (i+1)) A hA

/-- One concrete finite list supplies every label slot simultaneously. Its
entries all centralize the same density and fix the same support complement. -/
theorem label_allocation {P : Presentation} (R : StructuralRealization P) :
    ∃ E : List Op,E.length=encodingCount P ∧
      (∀ U ∈ E,Unitary U ∧ Centralizes R.density.op U ∧ (U-1)*(1-R.support)=0) ∧
      (∀ i : Fin P.types.length,
        decodeEncoding R.support
          (E[encodingOffset P i.val]?.getD 1)
          (E[encodingOffset P i.val+1]?.getD 1) P.types[i.val]=R.label i.val ∧
        (P.types[i.val]=.projection →
          (E[encodingOffset P i.val]?.getD 1)*(E[encodingOffset P i.val]?.getD 1)=1)) := by
  have hs : Preliminaries.SupportOf R.density R.support :=
    ⟨R.support_projection,R.density_supported,R.faithful_on⟩
  have h (i : Fin P.types.length) := typed_encoding R.density R.support (R.label i.val) hs
    (R.label_supported i.val).2 (R.label_supported i.val).1 (R.centralizer i.val)
    P.types[i.val] (R.typed i)
  choose A B hA hB hcA hcB hfA hfB hd hr using h
  let U : ℕ → Op := fun i => if hi : i<P.types.length then A ⟨i,hi⟩ else 1
  let V : ℕ → Op := fun i => if hi : i<P.types.length then B ⟨i,hi⟩ else 1
  let E := pack P.types U V
  have hfirst (i : Fin P.types.length) :
      E[encodingOffset P i.val]?=some (A i) := by
    change (pack P.types U V)[offset P.types i.val]?=some (A i)
    simpa only [U,dif_pos i.isLt] using pack_first P.types U V i.val i.isLt
  have hsecond (i : Fin P.types.length) (ht : P.types[i.val]=.contraction) :
      E[encodingOffset P i.val+1]?=some (B i) := by
    have hi : P.types[i.val]?=some .contraction := by simp [ht]
    change (pack P.types U V)[offset P.types i.val+1]?=some (B i)
    simpa only [V,dif_pos i.isLt] using pack_second P.types U V i.val hi
  refine ⟨E,?_,?_,?_⟩
  · change (pack P.types U V).length=(P.types.map width).sum
    exact pack_length P.types U V
  · apply pack_property P.types U V
    · intro i
      dsimp only [U]
      split_ifs with hi
      · exact ⟨hA _,hcA _,hfA _⟩
      · simp [Unitary,Centralizes]
    · intro i
      dsimp only [V]
      split_ifs with hi
      · exact ⟨hB _,hcB _,hfB _⟩
      · simp [Unitary,Centralizes]
  · intro i
    rw [hfirst]
    simp only [Option.getD_some]
    constructor
    · cases ht : P.types[i.val]
      · simpa only [ht,decodeEncoding] using hd i
      · simpa only [ht,decodeEncoding] using hd i
      · simpa only [ht,decodeEncoding] using hd i
      · rw [hsecond i ht]
        simpa only [ht,Option.getD_some] using hd i
    · exact hr i

#print axioms pack_first
#print axioms pack_second
#print axioms label_allocation
end Sigma2.CompilerHonestAllocation
