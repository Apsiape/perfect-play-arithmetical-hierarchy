import Sigma2.RowCompletenessMirrors

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowCompleteness
open Compiler RowGame TensorLifts Preliminaries

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩


/-- Synchronized mirrors make zero events symmetric, using positivity and the
actual vector. No commutation of two Alice measurements is assumed. -/
theorem reverse_zero (A B C D : Op) (hA : Positive A) (hB : Positive B)
    (hC : Positive C) (hD : Positive D) (v : AB)
    (hmA : left A v=right D v) (hmB : right B v=left C v)
    (hz : (left C*right D) v=0) : (left A*right B) v=0 := by
  apply positive_apply_eq_zero _ (joint_positive A B hA hB)
  have he : inner ℂ v ((left A*right B) v)=0 := by
    calc
      inner ℂ v ((left A*right B) v)=inner ℂ (left A v) (right B v) :=
        ((left_positive A hA).isSymmetric v (right B v)).symm
      _ = inner ℂ (right D v) (left C v) := by rw [hmA,hmB]
      _ = inner ℂ v (right D (left C v)) := (right_positive D hD).isSymmetric v (left C v)
      _ = inner ℂ v ((left C*right D) v) := by rw [← mul_apply_eq_comp,← commute]
      _ = 0 := by rw [hz,inner_zero_right]
  exact congrArg Complex.re he

/-- The equality test is killed by the actual same-question projective partition. -/
theorem synchronized_diagonal_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (P Q : Partition Op ι) (v : AB)
    (hm : ∀ a,left (P.effect a) v=right (Q.effect a) v) (a b : ι) (hne : a≠b) :
    (left (P.effect a)*right (Q.effect b)) v=0 := by
  change left (P.effect a) (right (Q.effect b) v)=0
  rw [← hm b]
  change (left (P.effect a)*left (P.effect b)) v=0
  rw [← left_mul,P.orthogonal a b hne,CoarseCells.left_zero,zero_apply]

/-- Exact Boolean new/new rejection case split for the constructed simultaneous
family. The remaining input consists solely of the directed table bindings. -/
theorem newRule_zero_of_directed (G : Game) (R : Rows G.scenario) (E F : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (v : AB)
    (hm : ∀ i,left (E i) v=right (F i) v)
    (hd : ∀ q p,q ∈ questions R → p ∈ questions R → ∀ a b,directed R q p a.val b.val=false →
      (left ((newPartition G R E hE q).effect a)*right ((newPartition G R F hF p).effect b))
        (FiniteAncilla.entangle (RowSlots.dimension R) v)=0)
    (q p : Q R) (hq : q ∈ questions R) (hp : p ∈ questions R) (a b : AA (scenario G R)) (hz : newRule R q p a.val b.val=false) :
    (left ((newPartition G R E hE q).effect a)*right ((newPartition G R F hF p).effect b))
      (FiniteAncilla.entangle (RowSlots.dimension R) v)=0 := by
  let w := FiniteAncilla.entangle (RowSlots.dimension R) v
  by_contra hprod
  have hvq : valid R q a.val=true := by
    cases hh : valid R q a.val
    · have he := newPartition_invalid G R E hE q a hh
      simp only [he,CoarseCells.left_zero,zero_mul,zero_apply] at hprod
      exact False.elim (hprod trivial)
    · rfl
  have hvp : valid R p b.val=true := by
    cases hh : valid R p b.val
    · have he := newPartition_invalid G R F hF p b hh
      simp only [he,CoarseCells.right_zero,mul_zero,zero_apply] at hprod
      exact False.elim (hprod trivial)
    · rfl
  have heq : (if q=p then decide (a.val=b.val) else true)=true := by
    by_cases hqp : q=p
    · subst p
      rw [ite_eq_left rfl,decide_eq_true_eq]
      by_contra hne
      apply hprod
      apply synchronized_diagonal_zero (newPartition G R E hE q) (newPartition G R F hF q) w
        (newPartition_mirror G R E F hE hF v hm q)
      intro hab
      exact hne (congrArg Fin.val hab)
    · simp [hqp]
  have hqp : directed R q p a.val b.val=true := by
    cases hh : directed R q p a.val b.val
    · exact False.elim (hprod (hd q p hq hp a b hh))
    · rfl
  have hpq : directed R p q b.val a.val=true := by
    cases hh : directed R p q b.val a.val
    · apply False.elim
      apply hprod
      apply reverse_zero _ _ _ _
        ((newPartition G R E hE q).positive a) ((newPartition G R F hF p).positive b)
        ((newPartition G R E hE p).positive b) ((newPartition G R F hF q).positive a) w
      · exact newPartition_mirror G R E F hE hF v hm q a
      · exact (newPartition_mirror G R E F hE hF v hm p b).symm
      · exact hd p q hp hq b a hh
    · rfl
  have ht : newRule R q p a.val b.val=true := by simp only [newRule,hvq,hvp,heq,hqp,hpq,Bool.true_and]
  rw [hz] at ht
  contradiction

end Sigma2.RowCompleteness
