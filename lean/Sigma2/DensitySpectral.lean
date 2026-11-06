import Sigma2.Coefficients
import Mathlib.Analysis.InnerProductSpace.Spectrum

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.DensitySpectral

/-- Rank-one operators are compact, by factoring through the scalar field. -/
theorem rankOne_compact (u v : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ u v) := by
  have hh := (isCompactOperator_of_locallyCompactSpace_dom (innerSL ℂ v)).clm_comp
    ((1 : ℂ →L[ℂ] ℂ).smulRight u)
  exact hh

/-- A covariance with finite total column mass is compact in operator norm. -/
theorem covariance_compact (u : ℕ → H) (hu : Summable (fun i => ‖u i‖^2)) :
    IsCompactOperator (Coefficients.covariance u) := by
  apply isClosed_setOfPred_isCompactOperator.mem_of_tendsto
    (Coefficients.summable_rankOne u hu).hasSum
  exact Filter.Eventually.of_forall (fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      change IsCompactOperator (fun v => InnerProductSpace.rankOne ℂ (u i) (u i) v +
        (∑ j ∈ s, InnerProductSpace.rankOne ℂ (u j) (u j)) v)
      exact (rankOne_compact (u i) (u i)).add ih)

/-- The square-root columns already used for purification recover the density
as an operator-norm sum, without assuming spectral data in `Density`. -/
theorem eq_covariance (h : Density) :
    h.op=Coefficients.covariance (fun i => Coefficients.positiveRoot h.op (basis i)) := by
  let u : ℕ → H := fun i => Coefficients.positiveRoot h.op (basis i)
  have hu : Summable (fun i => ‖u i‖^2) := by
    convert h.diagonal_summable using 1
    funext i
    simpa [u,basis,entry,lp.inner_single_left] using
      Coefficients.sqrt_column_norm_sq h.op h.positive i
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro v
  exact (Coefficients.sqrt_columns h.op h.positive v w).unique
    (Coefficients.covariance_hasSum u hu v w)

/-- Positivity and summable diagonal imply compactness for the project's exact
normal-density interface. -/
theorem compact (h : Density) : IsCompactOperator h.op := by
  rw [eq_covariance h]
  apply covariance_compact
  convert h.diagonal_summable using 1
  funext i
  simpa [basis,entry,lp.inner_single_left] using
    Coefficients.sqrt_column_norm_sq h.op h.positive i

abbrev block (h : Density) (μ : ℂ) := Module.End.eigenspace h.op.toLinearMap μ

theorem finite_block (h : Density) (μ : ℂ) (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (block h μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (compact h) μ hμ

/-- Commutation preserves each actual density eigenspace. -/
theorem block_invariant (h : Density) (T : Op) (hc : Centralizes h.op T) (μ : ℂ)
    (v : H) (hv : v ∈ block h μ) : T v ∈ block h μ := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  change h.op v=μ • v at hv
  change h.op (T v)=μ • T v
  calc
    h.op (T v) = T (h.op v) := congrArg (fun A : Op => A v) hc
    _ = μ • T v := by rw [hv,map_smul]

/-- Faithfulness removes the zero eigenspace. -/
theorem zero_block (h : Density) (hf : Faithful h) : block h 0=⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  rw [Submodule.mem_bot]
  apply hf
  rw [Module.End.mem_eigenspace_iff] at hv
  change h.op v=0 • v at hv
  simpa only [zero_smul,map_zero] using hv

/-- Compact self-adjoint spectral completeness on the actual model. -/
theorem blocks_total (h : Density) :
    (⨆ μ : ℂ, block h μ)ᗮ=⊥ :=
  ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (compact h) h.positive.isSymmetric

#print axioms compact
#print axioms finite_block
#print axioms block_invariant
#print axioms blocks_total
end Sigma2.DensitySpectral

