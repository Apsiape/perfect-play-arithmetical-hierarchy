import Sigma2.Statements
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

set_option synthInstance.maxHeartbeats 10000
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal CStarAlgebra
open Function
namespace Sigma2.Coefficients

/-- A separable Hilbert space has at most countably many orthonormal vectors. -/
theorem orthonormal_countable {E ι : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [TopologicalSpace.SeparableSpace E]
    {v : ι → E} (hv : Orthonormal ℂ v) : Countable ι := by
  have hd : Pairwise (Disjoint on (fun i => Metric.ball (v i) (1/2 : ℝ))) := by
    intro i j hij
    apply Metric.ball_disjoint_ball
    have hn := norm_sub_sq (𝕜 := ℂ) (v i) (v j)
    rw [hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij] at hn
    simp only [map_zero] at hn
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i-v j)]
  exact hd.countable_of_isOpen_disjoint (fun _ => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)

/-- Extend square-summable coefficients by zero along an injection. -/
def embed {ι κ : Type} (f : ι ↪ κ) :
    lp (fun _ : ι => ℂ) 2 →ₗᵢ[ℂ] lp (fun _ : κ => ℂ) 2 :=
  (((HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ
    (lp (fun _ : κ => ℂ) 2))).orthonormal).comp f f.injective).orthogonalFamily.linearIsometry

theorem separable_embedding (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    Nonempty (E →ₗᵢ[ℂ] H) := by
  classical
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ E
  let : Countable w := orthonormal_countable b.orthonormal
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat w
  exact ⟨(embed ⟨f,hf⟩).comp b.repr.toLinearIsometry⟩




variable {ι κ : Type}
abbrev Space (κ : Type) := lp (fun _ : κ => ℂ) 2

local instance : SMul ℝ (Space κ →L[ℂ] Space κ) :=
  (Module.restrictScalars ℝ ℂ (Space κ →L[ℂ] Space κ)).toSMul
local instance : Module ℝ (Space κ →L[ℂ] Space κ) := Module.restrictScalars ℝ ℂ _
local instance : Algebra ℝ (Space κ →L[ℂ] Space κ) := Algebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ (Space κ →L[ℂ] Space κ) := NormedSpace.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (Space κ →L[ℂ] Space κ) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : IsScalarTower ℝ ℂ (Space κ →L[ℂ] Space κ) where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A = (r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A

/-- A square-summable family gives a norm-convergent sum of positive rank-one operators. -/
theorem summable_rankOne (u : ι → Space κ) (hu : Summable (fun i => ‖u i‖^2)) :
    Summable (fun i => InnerProductSpace.rankOne ℂ (u i) (u i)) := by
  apply Summable.of_norm
  simpa only [InnerProductSpace.norm_rankOne, pow_two] using hu

def covariance (u : ι → Space κ) : Space κ →L[ℂ] Space κ :=
  ∑' i, InnerProductSpace.rankOne ℂ (u i) (u i)

theorem covariance_positive (u : ι → Space κ) : (covariance u).IsPositive := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  exact tsum_nonneg (fun i => ContinuousLinearMap.nonneg_iff_isPositive.mpr
    (InnerProductSpace.isPositive_rankOne_self (u i)))

theorem covariance_hasSum (u : ι → Space κ) (hu : Summable (fun i => ‖u i‖^2))
    (v w : Space κ) :
    HasSum (fun i => inner ℂ v (u i) * inner ℂ (u i) w)
      (inner ℂ v (covariance u w)) := by
  have hh := ((summable_rankOne u hu).hasSum.mapL
    (ContinuousLinearMap.apply ℂ (Space κ) w)).mapL (innerSL ℂ v)
  simpa only [ContinuousLinearMap.apply_apply, innerSL_apply_apply,
    InnerProductSpace.inner_right_rankOne_apply, covariance] using hh

open scoped Classical in
theorem covariance_entry [DecidableEq κ] (u : ι → Space κ) (hu : Summable (fun i => ‖u i‖^2))
    (a b : κ) :
    covariance u (lp.single 2 b 1) a = ∑' i, u i a * star (u i b) := by
  have hh := covariance_hasSum u hu (lp.single 2 a 1) (lp.single 2 b 1)
  simpa [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
    mul_comm] using hh.tsum_eq.symm

theorem norm_sq_hasSum (v : Space κ) : HasSum (fun i => ‖v i‖^2) (‖v‖^2) := by
  simpa using lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) v


/-- The diagonal mass is absolutely summable in both indices. -/
theorem coefficient_mass_summable (u : ι → Space κ)
    (hu : Summable (fun i => ‖u i‖^2)) :
    Summable (fun ik : ι × κ => ‖u ik.1 ik.2‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  exact ⟨fun i => (norm_sq_hasSum (u i)).summable,
    by simpa only [(norm_sq_hasSum _).tsum_eq] using hu⟩

open scoped Classical in
theorem covariance_diagonal [DecidableEq κ] (u : ι → Space κ)
    (hu : Summable (fun i => ‖u i‖^2)) (a : κ) :
    (covariance u (lp.single 2 a 1) a).re = ∑' i, ‖u i a‖^2 := by
  have hh := (covariance_hasSum u hu (lp.single 2 a 1) (lp.single 2 a 1)).mapL Complex.reCLM
  simpa [lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using hh.tsum_eq.symm

open scoped Classical in
theorem covariance_trace [DecidableEq κ] (u : ι → Space κ) (hu : Summable (fun i => ‖u i‖^2)) :
    Summable (fun a => (covariance u (lp.single 2 a 1) a).re) ∧
    (∑' a, (covariance u (lp.single 2 a 1) a).re) = ∑' i, ‖u i‖^2 := by
  simp_rw [covariance_diagonal u hu]
  have hs := coefficient_mass_summable u hu
  refine ⟨hs.prod_symm.prod, ?_⟩
  rw [hs.tsum_comm]
  simp_rw [(norm_sq_hasSum _).tsum_eq]

def positiveRoot (T : Space κ →L[ℂ] Space κ) : Space κ →L[ℂ] Space κ := CFC.sqrt T

open scoped Classical in
/-- Parseval for a positive operator, using columns of its positive square root. -/
theorem sqrt_columns [DecidableEq κ] (T : Space κ →L[ℂ] Space κ) (hT : T.IsPositive)
    (v w : Space κ) :
    HasSum (fun i => inner ℂ v (positiveRoot T (lp.single 2 i 1)) *
      inner ℂ (positiveRoot T (lp.single 2 i 1)) w) (inner ℂ v (T w)) := by
  let A := positiveRoot T
  have hA : A.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)
  have hs : A*A=T := CFC.sqrt_mul_sqrt_self T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)
  let b : HilbertBasis κ ℂ (Space κ) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb (i : κ) : b i=lp.single 2 i 1 := b.repr_self i
  have hh := b.hasSum_inner_mul_inner (A v) (A w)
  have heq : inner ℂ (A v) (A w)=inner ℂ v (T w) := by
    rw [hA.inner_left_eq_inner_right v (A w)]
    change inner ℂ v ((A*A) w)=_
    rw [hs]
  rw [heq] at hh
  change HasSum (fun i => inner ℂ v (A (lp.single 2 i 1)) *
    inner ℂ (A (lp.single 2 i 1)) w) _
  convert hh using 1
  funext i
  rw [← hb i,hA.inner_left_eq_inner_right (b i) w,hA.inner_left_eq_inner_right v (b i)]

open scoped Classical in
theorem sqrt_column_norm_sq [DecidableEq κ] (T : Space κ →L[ℂ] Space κ) (hT : T.IsPositive) (i : κ) :
    ‖positiveRoot T (lp.single 2 i 1)‖^2 =
      (inner ℂ (lp.single 2 i 1) (T (lp.single 2 i 1))).re := by
  have hA : (positiveRoot T).IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg T)
  have hs : positiveRoot T*positiveRoot T=T :=
    CFC.sqrt_mul_sqrt_self T (ContinuousLinearMap.nonneg_iff_isPositive.mpr hT)
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [hA.inner_left_eq_inner_right]
  change (inner ℂ (lp.single 2 i 1) ((positiveRoot T*positiveRoot T) (lp.single 2 i 1))).re = _
  rw [hs]

#print axioms separable_embedding
#print axioms covariance_trace
#print axioms sqrt_columns
end Sigma2.Coefficients
