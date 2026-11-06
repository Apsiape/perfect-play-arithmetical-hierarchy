import Sigma2.RowCompletenessSupport
import Sigma2.RowSupportedRows

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns TensorLifts FiniteAncilla

/-- The original supported rational row vanishes on every positive-weight component,
including after replacement by the compressed named projection family. -/
theorem named_row_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hR : RowsHold R S) (E : Fin R.count → Op)
    (hE : ∀ i k,0<S.weight k →
      left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (r : Fin R.rowCount) (k : ℕ) (hk : 0<S.weight k) :
    left ((R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) • E i) (S.vector k)=0 := by
  obtain ⟨hA,hB,hmA,hmB,hmir,hrowA,hrowB⟩ := hR
  have hz := normal_left_zero S hA hmA _ (hrowA r) k hk
  have he : left ((R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) • E i) (S.vector k)=
      left ((R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) •
        S.measurements.alice (R.event i).x (R.event i).a) (S.vector k) := by
    simp only [DiagonalIdentification.left_add,MagicRelations.left_smul,left_sum,left_one,
      add_apply,smul_apply,sum_apply,
      one_apply_eq_self]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hE i k hk,measurements_left]
  exact he.trans hz

/-- The exact finite slot sum, with every cancelling padding pair included. -/
theorem finite_slot_sum {s} (R : Rows s) (r : Fin R.rowCount) (E : Fin R.count → Op) :
    (∑ j : Fin (RowSlots.dimension R),(RowSlots.slot R r j.val).eval E)=
      (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ)) •
        ((R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) • E i) := by
  have he := RowScalar.sum_getD ((RowSlots.slots R r).map (RowSlots.Slot.eval E))
    (RowSlots.dimension R) (by rw [List.length_map,RowSlots.slots_length])
    ((⟨none,false⟩ : RowSlots.Slot R.count).eval E)
  have hh : (∑ j : Fin (RowSlots.dimension R),(RowSlots.slot R r j.val).eval E)=
      ((RowSlots.slots R r).map (RowSlots.Slot.eval E)).sum := by
    simpa only [List.getElem?_map,Option.getD_map,RowSlots.slot] using he
  rw [hh,RowSlots.slots_sum]

theorem finite_slot_sum_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hR : RowsHold R S) (E : Fin R.count → Op)
    (hE : ∀ i k,0<S.weight k →
      left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (r : Fin R.rowCount) (k : ℕ) (hk : 0<S.weight k) :
    left (∑ j : Fin (RowSlots.dimension R),(RowSlots.slot R r j.val).eval E) (S.vector k)=0 := by
  rw [finite_slot_sum,MagicRelations.left_smul]
  change (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ)) • left _ (S.vector k)=0
  rw [named_row_zero G R S hR E hE r k hk,smul_zero]

/-- The zero Fourier outcome, as explicit constant operator-valued blocks. -/
def uniformBlocks (d : ℕ) : Matrix (Fin d) (Fin d) Op := fun _ _ => (1/(d:ℂ)) • (1:Op)

theorem uniform_mirror (d : ℕ) [NeZero d] (v : AB) :
    left (matrixOp d (uniformBlocks d)) (entangle d v)=
      right (matrixOp d (uniformBlocks d)) (entangle d v) := by
  apply matrix_mirror
  intro i j
  simp only [uniformBlocks,MagicRelations.left_smul,MagicRelations.right_smul,left_one,right_one]

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

/-- Exact row-column/reference product; no full-space row identity is assumed. -/
theorem column_uniform_entry {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount)
    (i j : Fin (RowSlots.dimension R)) :
    (rowColumn R E r 0*uniformBlocks (RowSlots.dimension R)) i j=
      ((1/(RowSlots.dimension R:ℂ))*(1/(RowSlots.dimension R:ℂ))) •
        ((RowSlots.slot R r i.val).eval E *
          ∑ k : Fin (RowSlots.dimension R),(RowSlots.slot R r k.val).eval E) := by
  simp only [Matrix.mul_apply,rowColumn,column,Fin.val_zero,RowParity.parity_zero,
    sign,Bool.false_eq_true,ite_false,mul_one,uniformBlocks,smul_mul_smul_comm,
    star_one,mul_one,slot_selfadjoint E hE]
  rw [← Finset.smul_sum,← Finset.mul_sum]

/-- Row-zero rejection holds on each original mixed component. -/
theorem column_reference_zero {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (v : AB)
    (hz : left (∑ j : Fin (RowSlots.dimension R),(RowSlots.slot R r j.val).eval E) v=0) :
    (left (columnEffect R E r 0)*right (matrixOp (RowSlots.dimension R)
      (uniformBlocks (RowSlots.dimension R)))) (entangle (RowSlots.dimension R) v)=0 := by
  change left (columnEffect R E r 0)
    (right (matrixOp _ _) (entangle _ v))=0
  rw [← uniform_mirror]
  change (left (matrixOp _ _)*left (matrixOp _ _)) (entangle _ v)=0
  rw [← left_mul,← matrixOp_mul]
  apply FiniteSum.ext_fiber (bipCoordinates (RowSlots.dimension R))
  intro ab
  rcases ab with ⟨a,b⟩
  rw [left_matrix_entangle,FiniteSum.fiber_zero,column_uniform_entry R E hE r a b,
    MagicRelations.left_smul,left_mul]
  change amplitude (RowSlots.dimension R) • (((1/(RowSlots.dimension R:ℂ))*(1/(RowSlots.dimension R:ℂ))) • left _ (left _ v))=0
  rw [hz,map_zero,smul_zero,smul_zero]

end Sigma2.RowCompleteness
