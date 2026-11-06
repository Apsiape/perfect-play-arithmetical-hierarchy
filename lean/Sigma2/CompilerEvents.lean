import Sigma2.CompilerEventLoss
import Sigma2.CompilerEventState

/-! The generic honest row-event interface. No clock development module is imported. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerEvents
open Compiler CompilerScaffold CompilerEventCounting CompilerEventState TensorLifts FiniteAncilla

/-- Concrete state/measurement data, not a probability or trace hypothesis.
Only occupied ensemble vectors need be specified or mirrored. -/
structure HonestRow {s₀ s : Scenario} (d : ℕ) [NeZero d]
    (S₀ : NormalStrategy s₀) (S : NormalStrategy s) (h : Density) (V : Fin d → Op)
    (xc xr : QA s) (yr yc : QB s) : Prop where
  marginal : MarginalA S₀ h
  weights : ∀ k,S.weight k=S₀.weight k
  vectors : ∀ k,S.weight k ≠ 0 → S.vector k=entangle d (S₀.vector k)
  unitary : ∀ j,Unitary (V j)
  aliceColumn : S.measurements.alice xc 0=matrixOp d (zeroColumn V)
  aliceReference : S.measurements.alice xr 0=matrixOp d (zeroReference d)
  bobReference : S.measurements.bob yr 0=matrixOp d (zeroReference d)
  bobColumnMirror : ∀ k,S.weight k ≠ 0 →
    right (S.measurements.bob yc 0) (S.vector k)=
      left (matrixOp d (zeroColumn V)) (S.vector k)

/-- The selfadjoint-sum hypothesis holds for the honest reflection slots.
It is separate from unitarity: arbitrary sums of unitaries need not be normal. -/
theorem forward_zero_probability {s₀ s} (d : ℕ) [NeZero d]
    (S₀ : NormalStrategy s₀) (S : NormalStrategy s) (h : Density) (V : Fin d → Op)
    (xc xr : QA s) (yr yc : QB s) (H : HonestRow d S₀ S h V xc xr yr yc)
    (hT : star (∑ j,V j)=∑ j,V j) :
    S.probability xc yr 0 0=
      (1/(d:ℝ)^3)*(trace (h.op*(star (∑ j,V j)*(∑ j,V j)))).re := by
  have hB : Positive (star (∑ j,V j)*(∑ j,V j)) :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (star_mul_self_nonneg _)
  rw [← normal_expectation S₀ h H.marginal _ hB,← tsum_mul_left]
  unfold NormalStrategy.probability
  apply tsum_congr
  intro k
  by_cases hw : S.weight k=0
  · have hw₀ : S₀.weight k=0 := (H.weights k).symm.trans hw
    simp only [hw,hw₀,zero_mul,mul_zero]
  · simp only [NormalStrategy.component,PureStrategy.probability,measurements_left,
      measurements_right,H.aliceColumn,H.bobReference,H.vectors k hw,mul_apply_eq_comp]
    rw [entangled_zero_expectation]
    have hc : (1/(d:ℂ)^3)=((1/(d:ℝ)^3:ℝ):ℂ) := by push_cast; rfl
    rw [hc]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,H.weights k,hT]
    ring

/-- Reversing the ordered questions conjugates the local projection overlap.
Its real part is equal, with no swap-invariance assumption on the old state. -/
theorem reverse_eq_forward {s₀ s} (d : ℕ) [NeZero d]
    (S₀ : NormalStrategy s₀) (S : NormalStrategy s) (h : Density) (V : Fin d → Op)
    (xc xr : QA s) (yr yc : QB s) (H : HonestRow d S₀ S h V xc xr yr yc) :
    S.probability xr yc 0 0=S.probability xc yr 0 0 := by
  have hC := zeroColumn_projection V H.unitary
  have hR : Projection (matrixOp d (zeroReference d)) := by
    have he : zeroReference d=zeroColumn (fun _ : Fin d => (1:Op)) := by
      ext i j; simp [zeroReference,zeroColumn]
    rw [he]
    exact zeroColumn_projection _ (fun _ => ⟨by simp,by simp⟩)
  have hCL := (left_positive _
    (ContinuousLinearMap.IsPositive.of_isStarProjection ⟨hC.2,hC.1⟩)).isSymmetric
  have hRL := (left_positive _
    (ContinuousLinearMap.IsPositive.of_isStarProjection ⟨hR.2,hR.1⟩)).isSymmetric
  unfold NormalStrategy.probability
  apply tsum_congr
  intro k
  by_cases hw : S.weight k=0
  · simp only [hw,zero_mul]
  · congr 1
    simp only [NormalStrategy.component,PureStrategy.probability,measurements_left,
      measurements_right,H.aliceReference,H.aliceColumn,H.bobReference,mul_apply_eq_comp]
    change (inner ℂ (S.vector k)
      (left (matrixOp d (zeroReference d)) (right (S.measurements.bob yc 0) (S.vector k)))).re=_
    rw [H.bobColumnMirror k hw]
    have hm : right (matrixOp d (zeroReference d)) (S.vector k)=
        left (matrixOp d (zeroReference d)) (S.vector k) := by
      rw [H.vectors k hw]
      exact (reference_mirror d _).symm
    rw [hm]
    calc
      _=(inner ℂ (left (matrixOp d (zeroReference d)) (S.vector k))
          (left (matrixOp d (zeroColumn V)) (S.vector k))).re :=
        congrArg Complex.re (hRL _ _).symm
      _=(inner ℂ (left (matrixOp d (zeroColumn V)) (S.vector k))
          (left (matrixOp d (zeroReference d)) (S.vector k))).re := inner_re_symm (𝕜 := ℂ) _ _
      _=_ := congrArg Complex.re (hCL _ _)

theorem row_zero_probabilities {s₀ s} (d : ℕ) [NeZero d]
    (S₀ : NormalStrategy s₀) (S : NormalStrategy s) (h : Density) (V : Fin d → Op)
    (xc xr : QA s) (yr yc : QB s) (H : HonestRow d S₀ S h V xc xr yr yc)
    (hT : star (∑ j,V j)=∑ j,V j) :
    let p := (1/(d:ℝ)^3)*(trace (h.op*(star (∑ j,V j)*(∑ j,V j)))).re
    S.probability xc yr 0 0=p ∧ S.probability xr yc 0 0=p := by
  dsimp only
  have hf := forward_zero_probability d S₀ S h V xc xr yr yc H hT
  exact ⟨hf,(reverse_eq_forward d S₀ S h V xc xr yr yc H).trans hf⟩

/-- The actual frozen final-game ordered summands, with corrected coefficient 8.
The abstract dimension is required to be the frozen RowSlots dimension. -/
theorem actual_row_loss {s₀} (P : Presentation) (r : Fin (rows P).rowCount)
    (d : ℕ) [NeZero d] (hd : d=RowSlots.dimension (rows P))
    (S₀ : NormalStrategy s₀) (S : NormalStrategy (finalGame P).scenario)
    (h : Density) (V : Fin d → Op)
    (H : HonestRow d S₀ S h V
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)))
    (L : ℕ) (A : Op) (hA : star A=A) (hc : Centralizes h.op A)
    (hv : ∑ j,V j=(2*(L:ℂ)) • A) :
    bothZeroContribution P S
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r))=
      8*(L:ℝ)^2/(d:ℝ)^3/(questionCount P:ℝ)^2*(trace (h.op*(A*A))).re := by
  have hT : star (∑ j,V j)=∑ j,V j := by
    rw [hv,star_smul,hA]
    congr 1
    simp
  have hp := row_zero_probabilities d S₀ S h V _ _ _ _ H hT
  dsimp only at hp
  rw [actual_both_zero_weight P r S _ hp.1 hp.2]
  exact doubled_row_loss_formula L d (hd.symm ▸ RowSlots.dimension_pos (rows P))
    A hA h hc V H.unitary hv _

#print axioms HonestRow
#print axioms forward_zero_probability
#print axioms reverse_eq_forward
#print axioms row_zero_probabilities
#print axioms actual_row_loss
end Sigma2.CompilerEvents
