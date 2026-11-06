import Sigma2.FiniteAncillaMatrix
import Sigma2.RowWalsh

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns RowWalsh FiniteAncilla TensorLifts

local instance columnsDimensionNeZero {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

/-- Actual bounded l2 effects for every honest row-column question. -/
def columnEffect {s} (R : Rows s) (E : Fin R.count → Op) (r : Fin R.rowCount)
    (a : Fin (RowSlots.dimension R)) : Op :=
  matrixOp (RowSlots.dimension R) (rowColumn R E r a)

theorem columnEffect_projection {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (a : Fin (RowSlots.dimension R)) :
    Projection (columnEffect R E r a) := by
  have h := rowColumn_projection R E hE r a
  exact matrixOp_projection _ _ h.1 h.2

theorem columnEffect_positive {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (a : Fin (RowSlots.dimension R)) :
    Positive (columnEffect R E r a) := by
  have h := columnEffect_projection R E hE r a
  exact ContinuousLinearMap.IsPositive.of_isStarProjection ⟨h.2,h.1⟩

theorem columnEffect_sum {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) :
    (∑ a,columnEffect R E r a)=1 := by
  change (∑ a,matrixOp (RowSlots.dimension R) (rowColumn R E r a))=1
  rw [← matrixOp_sum,(rowColumn_partition R E hE r).2.1,matrixOp_one]

theorem columnEffect_orthogonal {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount)
    (a b : Fin (RowSlots.dimension R)) (hab : a≠b) :
    columnEffect R E r a*columnEffect R E r b=0 := by
  change matrixOp _ _*matrixOp _ _=0
  rw [← matrixOp_mul,(rowColumn_partition R E hE r).2.2 a b hab,matrixOp_zero]

/-- A convenient full-scenario POVM for each row's honest column measurement. -/
def columnMeasurements {s} (R : Rows s) (E F : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (r : Fin R.rowCount) :
    Measurements ⟨0,0,RowSlots.dimension R-1,RowSlots.dimension R-1⟩ := by
  have hd : RowSlots.dimension R-1+1=RowSlots.dimension R := by
    have := RowSlots.dimension_pos R
    omega
  refine TensorLifts.measurements _
    (fun _ a => columnEffect R E r (Fin.cast hd a))
    (fun _ b => columnEffect R F r (Fin.cast hd b))
    (fun _ a => columnEffect_positive R E hE r _)
    (fun _ b => columnEffect_positive R F hF r _) ?_ ?_
  · intro x
    exact ((Equiv.sum_comp (finCongr hd) (columnEffect R E r)).trans
      (columnEffect_sum R E hE r))
  · intro y
    exact ((Equiv.sum_comp (finCongr hd) (columnEffect R F r)).trans
      (columnEffect_sum R F hF r))

theorem slot_eval_sign {n : ℕ} (E : Fin n → Op) (v : RowSlots.Slot n) :
    v.eval E=sign v.negative •
      (match v.event with | none => (1:Op) | some i => (2:ℂ) • E i-1) := by
  let U : Op := match v.event with | none => 1 | some i => (2:ℂ) • E i-1
  change (if v.negative then -U else U)=sign v.negative • U
  cases h : v.negative
  · change U=(1:ℂ) • U
    exact (one_smul ℂ U).symm
  · change -U=(-1:ℂ) • U
    exact (neg_one_smul ℂ U).symm

theorem slot_selfadjoint {n : ℕ} (E : Fin n → Op) (hE : ∀ i,Projection (E i))
    (v : RowSlots.Slot n) : star (v.eval E)=v.eval E := by
  rw [slot_eval_sign,star_smul,sign_star]
  congr 1
  cases he : v.event with
  | none => exact star_one Op
  | some i =>
    change star ((2:ℂ) • E i-1)=(2:ℂ) • E i-1
    have hs : star ((2:ℂ) • E i)=(2:ℂ) • E i := by
      simpa only [star_ofNat,(hE i).1] using star_smul (2:ℂ) (E i)
    exact (star_sub ((2:ℂ) • E i) (1:Op)).trans
      (congrArg₂ (fun A B : Op => A-B) hs (star_one Op))

theorem slot_mirror {n : ℕ} (E F : Fin n → Op) (v : AB)
    (hm : ∀ i,left (E i) v=right (F i) v) (s : RowSlots.Slot n) :
    left (s.eval E) v=right (s.eval F) v := by
  rw [slot_eval_sign,slot_eval_sign,MagicRelations.left_smul,MagicRelations.right_smul]
  change sign s.negative • left _ v=sign s.negative • right _ v
  congr 1
  cases he : s.event with
  | none => simp only [left_one,right_one]
  | some i =>
    rw [PureSupport.left_sub,MagicRelations.right_sub,MagicRelations.left_smul,
      MagicRelations.right_smul,left_one,right_one]
    change (2:ℂ) • left (E i) v-v=(2:ℂ) • right (F i) v-v
    rw [hm i]

/-- The concrete honest column effects synchronize on the entangled extension.
Bob's old products are reversed while the finite matrix coordinates transpose. -/
theorem columnEffect_mirror {s} (R : Rows s) (E F : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (v : AB)
    (hm : ∀ i,left (E i) v=right (F i) v) (r : Fin R.rowCount)
    (t : Fin (RowSlots.dimension R)) :
    left (columnEffect R E r t) (entangle (RowSlots.dimension R) v)=
      right (columnEffect R F r t) (entangle (RowSlots.dimension R) v) := by
  apply matrix_mirror
  intro i j
  let c : ℂ := 1/(RowSlots.dimension R:ℂ)
  let chi (k : Fin (RowSlots.dimension R)) : ℂ := sign (parity (2*RowSlots.squares R) t.val k.val)
  change left ((c*chi i*chi j) •
    ((RowSlots.slot R r i.val).eval E*star ((RowSlots.slot R r j.val).eval E))) v=
      right ((c*chi j*chi i) •
        ((RowSlots.slot R r j.val).eval F*star ((RowSlots.slot R r i.val).eval F))) v
  rw [slot_selfadjoint E hE,slot_selfadjoint F hF,
    MagicRelations.left_smul,MagicRelations.right_smul]
  have hc : c*chi i*chi j=c*chi j*chi i := by ring
  change (c*chi i*chi j) • left _ v=(c*chi j*chi i) • right _ v
  rw [hc]
  exact congrArg (fun w : AB => (c*chi j*chi i) • w)
    (product_mirror _ _ _ _ v (slot_mirror E F v hm _) (slot_mirror E F v hm _))

end Sigma2.RowCompleteness
