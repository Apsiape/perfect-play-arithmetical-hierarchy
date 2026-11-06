import Sigma2.RowZEntries
import Sigma2.RowSlotGraphs

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates FiniteJoint CoarseCells

def scalarAnswer (G : Game) (R : Rows G.scenario) (a : Fin (RowSlots.dimension R)) : Answer G R :=
  ⟨a.val,by have := a.isLt; dsimp [Answer,AA,scenario]; omega⟩

/-- The actual Z-bit spectral factor selects exactly its numerical register bit. -/
theorem axisZ_unit_action (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (k : Fin (2*RowSlots.squares R)) (negative : Bool)
    (i j : Register (RowSlots.squares R)) :
    axisEffect false G R S.measurements P false k negative*
        tensorUnit P (localUnit G R S.measurements P) i j=
      if Nat.testBit (registerFin _ i).val k.val=negative
        then tensorUnit P (localUnit G R S.measurements P) i j else 0 := by
  have hu := supportUnits_laws false G R S hS h hm P hP
  change Units P (tensorUnit P (localUnit G R S.measurements P)) at hu
  rw [axis_effect_formula false G R S hS h hm P hP]
  simp only [Bool.false_eq_true,ite_false,smul_mul_assoc,add_mul]
  rw [(hu.supported i j).1,measured_Z_bit_action G R S hS h hm P hP]
  cases negative <;> cases hb : Nat.testBit (registerFin _ i).val k.val <;>
    simp [hb,RowColumns.sign] <;> module

/-- Ordered spectral selectors require no unproved interchange of factors. -/
theorem intersection_selector {κ : Type} (P T : Op) (C : κ → Op) (f v : κ → Bool)
    (hP : P*T=T) (ha : ∀ k,C k*T=if f k=v k then T else 0) (ks : List κ) :
    intersection P C ks*T=if ∀ k ∈ ks,f k=v k then T else 0 := by
  induction ks with
  | nil => simpa [intersection] using hP
  | cons k ks ih =>
    rw [intersection,mul_assoc,ih]
    by_cases hh : ∀ l ∈ ks,f l=v l
    · rw [if_pos hh,ha]
      simp only [List.forall_mem_cons,and_iff_left hh]
    · simp [hh]

/-- Each actual global-Z outcome is its literal diagonal unit in the original
    common scalar algebra, with the exact table label. -/
theorem globalZ_diagonal_alice (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (a : Fin (RowSlots.dimension R)) :
    newEffects false G R S.measurements P (globalQ R false) (scalarAnswer G R a)=
      tensorUnit P (localUnit G R S.measurements P)
        ((registerFin _).symm a) ((registerFin _).symm a) := by
  let t := tensorUnit P (localUnit G R S.measurements P)
  let b := (registerFin (RowSlots.squares R)).symm a
  have hu := supportUnits_laws false G R S hS h hm P hP
  change Units P t at hu
  let C := newEffects false G R S.measurements P (globalQ R false) (scalarAnswer G R a)
  have hc (i : Register (RowSlots.squares R)) : C*t i i=if i=b then t i i else 0 := by
    dsimp only [C]
    rw [global_unique false G R S hS h hm P hP]
    simp only [globalJoint,scalarAnswer,a.isLt,ite_true]
    rw [intersection_selector P (t i i) _
      (fun k => Nat.testBit (registerFin _ i).val k.val) (fun k => Nat.testBit a.val k.val)
      (hu.supported i i).1 (fun k => axisZ_unit_action G R S hS h hm P hP k _ i i)]
    have he : (∀ k ∈ List.finRange (2*RowSlots.squares R),
        Nat.testBit (registerFin _ i).val k.val=Nat.testBit a.val k.val) ↔ i=b := by
      constructor
      · intro hh
        have hv : (registerFin _ i).val=a.val := by
          apply RowParity.bounded_ext (n:=2*RowSlots.squares R)
          · rw [← dimension_bits R]
            change (registerFin _ i).val<4^RowSlots.squares R
            exact (registerFin _ i).isLt
          · rw [← dimension_bits R]; exact a.isLt
          · intro k hk; exact hh ⟨k,hk⟩ (List.mem_finRange _)
        apply (registerFin _).injective
        rw [show registerFin _ b=a from (registerFin _).apply_symm_apply a]
        exact Fin.ext hv
      · intro hi
        subst i
        simp only [b,Equiv.apply_symm_apply]
        simp
    simp only [he]
  have hr : C*P=C := (new_fine_supported false G R S.measurements P hP.1 _ _).2
  change C=t b b
  calc
    C = C*P := hr.symm
    _ = C*(∑ i,t i i) := by rw [hu.total]
    _ = ∑ i,if i=b then t i i else 0 := by simp only [Finset.mul_sum,hc]
    _ = t b b := by simp

#print axioms axisZ_unit_action
#print axioms intersection_selector
#print axioms globalZ_diagonal_alice
end Sigma2.RowScalar
