import Sigma2.RowQubitEntries

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates FiniteJoint CoarseCells

def registerSquare : {n : ℕ} → Register n → Fin n → FourUnits.Index
  | 0,_,g => Fin.elim0 g
  | n+1,i,g => Fin.cases i.1 (fun g => registerSquare i.2 g) g

/-- A table bit and its recursive square coordinate have exactly the same value. -/
theorem registerBit_square (n : ℕ) (i : Register n) (g : Fin n) (k : Fin 2) :
    registerBit i ⟨2*g.val+k.val,by have := g.isLt; have := k.isLt; omega⟩=
      indexBit (registerSquare i g) k := by
  induction n with
  | zero => exact Fin.elim0 g
  | succ n ih =>
    refine Fin.cases ?_ (fun g => ?_) g
    · fin_cases k <;> simp [registerBit,registerSquare,indexBit]
    · have hn : ¬2*g.succ.val+k.val<2 := by simp; omega
      have he : 2*g.succ.val+k.val-2=2*g.val+k.val := by simp; omega
      simpa only [registerBit,dif_neg hn,he,registerSquare,Fin.cases_succ] using ih i.2 g

/-- A local scalar eigenvalue acts on the same square in the common tensor
    units. Only commutation with the other scalar factors is used. -/
theorem tensor_diagonal_action (P A : Op) {n : ℕ}
    (U : Fin n → FourUnits.Index → FourUnits.Index → Op) (g : Fin n) (k : Fin 2)
    (hc : ∀ u,u≠g → ∀ a b,Commute A (U u a b))
    (ha : ∀ a b,A*U g a b=RowColumns.sign (indexBit a k) • U g a b)
    (i j : Register n) :
    A*tensorUnit P U i j=RowColumns.sign (indexBit (registerSquare i g) k) • tensorUnit P U i j := by
  induction n with
  | zero => exact Fin.elim0 g
  | succ n ih =>
    revert hc ha
    refine Fin.cases ?_ (fun g => ?_) g
    · intro hc ha
      change A*(U 0 i.1 j.1*tensorUnit P (fun u => U u.succ) i.2 j.2)=_
      rw [← mul_assoc,ha,smul_mul_assoc]
      rfl
    · intro hc ha
      have h0 : (0:Fin (n+1))≠g.succ := by intro h; have := congrArg Fin.val h; simp at this
      change A*(U 0 i.1 j.1*tensorUnit P (fun u => U u.succ) i.2 j.2)=_
      rw [← mul_assoc,(hc 0 h0 i.1 j.1).eq,mul_assoc]
      rw [ih (fun u => U u.succ) g
        (fun u hu => hc u.succ (by intro h; exact hu (Fin.succ_injective _ h))) ha i.2 j.2,
        mul_smul_comm]
      rfl

/-- Every actual measured Z axis has its literal diagonal-bit action on the
    previously constructed common support units. -/
theorem measured_Z_tensor_action (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) (k : Fin 2)
    (i j : Register (RowSlots.squares R)) :
    binary G R S.measurements P (axisQ R g (globalAxis false k))*
        tensorUnit P (localUnit G R S.measurements P) i j=
      RowColumns.sign (indexBit (registerSquare i g) k) •
        tensorUnit P (localUnit G R S.measurements P) i j := by
  apply tensor_diagonal_action
  · intro u hug a b
    have hs := binary_supported G R S.measurements P hP.1 (axisQ R g (globalAxis false k))
    apply commute_localUnit G R S.measurements P _ u (hs.2.trans hs.1.symm)
    intro l
    exact cross_commute G R S hS h hm P hP g u (Ne.symm hug) (globalAxis false k) l
  · intro a b
    simpa only [Bool.false_eq_true,ite_false] using
      measured_axis_local_action G R S hS h hm P hP g false k a b

/-- The actual table's Z-bit axis, indexed by the exact numerical table bit. -/
theorem measured_Z_bit_action (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (k : Fin (2*RowSlots.squares R)) (i j : Register (RowSlots.squares R)) :
    binary G R S.measurements P (bitAxis R false k)*
        tensorUnit P (localUnit G R S.measurements P) i j=
      RowColumns.sign (Nat.testBit (registerFin _ i).val k.val) •
        tensorUnit P (localUnit G R S.measurements P) i j := by
  rw [registerFin_testBit]
  have hg : k.val/2<RowSlots.squares R := by have := k.isLt; omega
  have he : 2*(k.val/2)+k.val%2=k.val := by omega
  have hh := measured_Z_tensor_action G R S hS h hm P hP ⟨k.val/2,hg⟩
    ⟨k.val%2,Nat.mod_lt _ (by decide)⟩ i j
  have hb := registerBit_square (RowSlots.squares R) i ⟨k.val/2,hg⟩
    ⟨k.val%2,Nat.mod_lt _ (by decide)⟩
  simp only [Fin.val_mk,he] at hb
  rw [← hb] at hh
  exact hh

#print axioms registerBit_square
#print axioms tensor_diagonal_action
#print axioms measured_Z_tensor_action
#print axioms measured_Z_bit_action
end Sigma2.RowScalar
