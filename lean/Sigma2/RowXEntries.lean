import Sigma2.RowDiagonalEntries
import Sigma2.RowWalsh

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates CoarseCells FiniteJoint RowColumns RowWalsh

/-- Flip the specified Pauli coordinate in the original recursive register. -/
def registerFlip : {n : ℕ} → Fin n → Fin 2 → Register n → Register n
  | 0,g,_,_ => Fin.elim0 g
  | n+1,g,k,i => Fin.cases (indexFlip i.1 k,i.2)
      (fun g => (i.1,registerFlip g k i.2)) g

theorem registerFlip_involutive {n : ℕ} (g : Fin n) (k : Fin 2) :
    Function.Involutive (registerFlip g k) := by
  intro i
  induction n with
  | zero => exact Fin.elim0 g
  | succ n ih =>
    refine Fin.cases ?_ (fun g => ?_) g
    · fin_cases k <;> rcases i with ⟨⟨a,b⟩,i⟩ <;> fin_cases a <;> fin_cases b <;>
        simp [registerFlip,indexFlip,PauliMatrixUnits.flip]
    · change (i.1,registerFlip g k (registerFlip g k i.2))=i
      rw [ih g]
      exact Prod.eta i

def registerFlipEquiv {n : ℕ} (g : Fin n) (k : Fin 2) : Equiv.Perm (Register n) :=
  (registerFlip_involutive g k).toPerm

/-- Cross-square commutation propagates the local transition action without
    requiring any new commutation inside a square. -/
theorem tensor_transition_action (P A : Op) {n : ℕ}
    (U : Fin n → FourUnits.Index → FourUnits.Index → Op) (g : Fin n) (k : Fin 2)
    (hc : ∀ u,u≠g → ∀ a b,Commute A (U u a b))
    (ha : ∀ a b,A*U g a b=U g (indexFlip a k) b)
    (i j : Register n) :
    A*tensorUnit P U i j=tensorUnit P U (registerFlip g k i) j := by
  induction n with
  | zero => exact Fin.elim0 g
  | succ n ih =>
    revert hc ha
    refine Fin.cases ?_ (fun g => ?_) g
    · intro hc ha
      change A*(U 0 i.1 j.1*tensorUnit P (fun u => U u.succ) i.2 j.2)=_
      rw [← mul_assoc,ha]
      rfl
    · intro hc ha
      have h0 : (0:Fin (n+1))≠g.succ := by intro h; have := congrArg Fin.val h; simp at this
      change A*(U 0 i.1 j.1*tensorUnit P (fun u => U u.succ) i.2 j.2)=_
      rw [← mul_assoc,(hc 0 h0 i.1 j.1).eq,mul_assoc]
      rw [ih (fun u => U u.succ) g
        (fun u hu => hc u.succ (by intro h; exact hu (Fin.succ_injective _ h))) ha i.2 j.2]
      rfl

theorem measured_X_tensor_action (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) (k : Fin 2)
    (i j : Register (RowSlots.squares R)) :
    binary G R S.measurements P (axisQ R g (globalAxis true k))*
        tensorUnit P (localUnit G R S.measurements P) i j=
      tensorUnit P (localUnit G R S.measurements P) (registerFlip g k i) j := by
  apply tensor_transition_action
  · intro u hug a b
    have hs := binary_supported G R S.measurements P hP.1 (axisQ R g (globalAxis true k))
    apply commute_localUnit G R S.measurements P _ u (hs.2.trans hs.1.symm)
    intro l
    exact cross_commute G R S hS h hm P hP g u (Ne.symm hug) (globalAxis true k) l
  · intro a b
    simpa only [Bool.true_eq,ite_true] using
      measured_axis_local_action G R S hS h hm P hP g true k a b

/-- Every recursive bit is changed exactly at the selected table position. -/
theorem registerBit_flip {n : ℕ} (g : Fin n) (k : Fin 2) (i : Register n) (l : Fin (2*n)) :
    registerBit (registerFlip g k i) l=
      Bool.xor (registerBit i l) (decide (l.val=2*g.val+k.val)) := by
  induction n with
  | zero => exact Fin.elim0 g
  | succ n ih =>
    refine Fin.cases ?_ (fun g => ?_) g
    · by_cases hl : l.val<2
      · have hl' : l.val=0 ∨ l.val=1 := by omega
        rcases hl' with hl' | hl' <;> fin_cases k <;> rcases i with ⟨⟨a,b⟩,i⟩ <;>
          fin_cases a <;> fin_cases b <;> simp [registerBit,registerFlip,indexFlip,PauliMatrixUnits.flip,hl,hl']
      · have hne : l.val≠2*(0:Fin (n+1)).val+k.val := by have := k.isLt; simp; omega
        simp only [registerFlip,Fin.cases_zero,registerBit,dif_neg hl,decide_eq_false hne,Bool.xor_false]
    · by_cases hl : l.val<2
      · have hne : l.val≠2*g.succ.val+k.val := by simp; omega
        simp only [registerFlip,Fin.cases_succ,registerBit,dif_pos hl,decide_eq_false hne,Bool.xor_false]
      · have he : (l.val-2=2*g.val+k.val) ↔ (l.val=2*g.succ.val+k.val) := by simp; omega
        simpa only [registerFlip,Fin.cases_succ,registerBit,dif_neg hl,Fin.val_mk,he] using
          ih g i.2 ⟨l.val-2,by have := l.isLt; omega⟩

/-- The recursive flip is the literal numerical xor used by the Boolean table. -/
theorem registerFin_flip {n : ℕ} (g : Fin n) (k : Fin 2) (i : Register n) :
    (registerFin n (registerFlip g k i)).val=Nat.xor (registerFin n i).val (2^(2*g.val+k.val)) := by
  have hd : 4^n=2^(2*n) := by rw [pow_mul]; norm_num
  have hk : 2*g.val+k.val<2*n := by have := g.isLt; have := k.isLt; omega
  apply RowParity.bounded_ext
    (by rw [← hd]; exact (registerFin n _).isLt)
    (RowParity.xor_bound (by rw [← hd]; exact (registerFin n i).isLt)
      (Nat.pow_lt_pow_right (by decide) hk))
  intro l hl
  rw [Nat.xor_eq,Nat.testBit_xor]
  rw [registerFin_testBit n _ ⟨l,hl⟩,registerFin_testBit n i ⟨l,hl⟩,registerBit_flip]
  by_cases he : l=2*g.val+k.val
  · subst l; simp
  · rw [Nat.testBit_two_pow_of_ne (Ne.symm he)]
    simp [he]

#print axioms registerFlip_involutive
#print axioms tensor_transition_action
#print axioms measured_X_tensor_action
#print axioms registerBit_flip
#print axioms registerFin_flip
end Sigma2.RowScalar