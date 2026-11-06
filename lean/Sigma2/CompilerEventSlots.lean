import Sigma2.CompilerEvents
import Sigma2.RowCompletenessColumns

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerEventSlots
open Compiler CompilerScaffold CompilerEventCounting CompilerEventState CompilerEvents

/-- The operator of the actual rational row, before denominator clearing. -/
def rowOperator {s} (R : Rows s) (E : Fin R.count → Op) (r : Fin R.rowCount) : Op :=
  (R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) • E i

def slotFamily {s} (R : Rows s) (E : Fin R.count → Op) (r : Fin R.rowCount)
    (j : Fin (RowSlots.dimension R)) : Op := (RowSlots.slot R r j.val).eval E

/-- Fin-sum/list-sum bridge for the literal padded slot enumeration. -/
theorem slotFamily_sum {s} (R : Rows s) (E : Fin R.count → Op) (r : Fin R.rowCount) :
    (∑ j,slotFamily R E r j)=
      (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ)) • rowOperator R E r := by
  let f : Fin (RowSlots.slots R r).length → Op :=
    fun j => ((RowSlots.slots R r)[j.val]).eval E
  have hl := RowSlots.slots_length R r
  have he : (∑ j,slotFamily R E r j)=∑ j,f (finCongr hl.symm j) := by
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [slotFamily,RowSlots.slot,f,finCongr]
    rw [List.getElem?_eq_getElem (show j.val<(RowSlots.slots R r).length by rw [hl]; exact j.isLt)]
    rfl
  rw [he,Equiv.sum_comp]
  have hs : (∑ j,f j)=((RowSlots.slots R r).map (RowSlots.Slot.eval E)).sum := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map _ _)
  rw [hs,RowSlots.slots_sum]
  rfl

theorem slotFamily_unitary {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) :
    ∀ j,Unitary (slotFamily R E r j) :=
  fun j => RowColumns.slot_unitary E hE (RowSlots.slot R r j.val)

theorem slotFamily_selfadjoint {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) :
    star (∑ j,slotFamily R E r j)=∑ j,slotFamily R E r j := by
  rw [show star (∑ j,slotFamily R E r j)=∑ j,star (slotFamily R E r j) from
    map_sum (starAddEquiv : Op ≃+ Op) _ Finset.univ]
  apply Finset.sum_congr rfl
  intro j hj
  exact RowCompleteness.slot_selfadjoint E hE _

/-- The abstract zero-column matrix is literally the frozen honest column at 0. -/
theorem rowColumn_zero {s} (R : Rows s) (E : Fin R.count → Op) (r : Fin R.rowCount) :
    RowColumns.rowColumn R E r 0=zeroColumn (slotFamily R E r) := by
  ext i j
  simp [RowColumns.rowColumn,RowColumns.column,zeroColumn,slotFamily,
    RowParity.parity_zero,RowColumns.sign]

theorem rowOperator_selfadjoint {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) :
    star (rowOperator R E r)=rowOperator R E r := by
  have hs := slotFamily_selfadjoint R E hE r
  rw [slotFamily_sum] at hs
  have hc : star (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ))=
      2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ) := by simp
  rw [star_smul,hc] at hs
  have hn : (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ))≠0 :=
    mul_ne_zero (by norm_num) (by
      exact_mod_cast ne_of_gt (RowSlots.denominator_pos (RowSlots.coefficients R r)))
  have he := congrArg (fun B : Op =>
    (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ))⁻¹ • B) hs
  simpa only [smul_smul,inv_mul_cancel₀ hn,one_smul] using he

theorem rowOperator_centralizes {s} (R : Rows s) (E : Fin R.count → Op)
    (h : Density) (hE : ∀ i,Centralizes h.op (E i)) (r : Fin R.rowCount) :
    Centralizes h.op (rowOperator R E r) := by
  unfold Centralizes rowOperator
  simp only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul,
    Finset.mul_sum,Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [show h.op*E i=E i*h.op from hE i]

local instance rowDimensionNeZero {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

/-- Ready-to-use specialization: d, L, V, A are all the literal frozen row data.
The caller supplies only the honest state/measurement record and centralizing
projection dictionary. No finite/list conversion or trace identity remains. -/
theorem actual_slot_row_loss {s₀} (P : Presentation) (r : Fin (rows P).rowCount)
    (S₀ : NormalStrategy s₀) (S : NormalStrategy (finalGame P).scenario)
    (h : Density) (E : Fin (rows P).count → Op) (hE : ∀ i,Projection (E i))
    (hc : ∀ i,Centralizes h.op (E i))
    (H : HonestRow (RowSlots.dimension (rows P)) S₀ S h (slotFamily (rows P) E r)
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r))) :
    bothZeroContribution P S
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r))=
      8*(RowSlots.denominator (RowSlots.coefficients (rows P) r):ℝ)^2/
        (RowSlots.dimension (rows P):ℝ)^3/(questionCount P:ℝ)^2*
          (trace (h.op*(rowOperator (rows P) E r*rowOperator (rows P) E r))).re := by
  exact actual_row_loss P r _ rfl S₀ S h _ H _ _
    (rowOperator_selfadjoint (rows P) E hE r)
    (rowOperator_centralizes (rows P) E h hc r) (slotFamily_sum (rows P) E r)

#print axioms actual_slot_row_loss
#print axioms rowOperator
#print axioms slotFamily
#print axioms slotFamily_sum
#print axioms slotFamily_unitary
#print axioms slotFamily_selfadjoint
#print axioms rowColumn_zero
#print axioms rowOperator_selfadjoint
#print axioms rowOperator_centralizes
end Sigma2.CompilerEventSlots
