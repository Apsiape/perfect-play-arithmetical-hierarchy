import Sigma2.Coefficients
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.LinearAlgebra.Isomorphisms

noncomputable section
open scoped InnerProductSpace
namespace Sigma2.FiniteContraction
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : SMul ℝ (E →L[ℂ] E) := (Module.restrictScalars ℝ ℂ (E →L[ℂ] E)).toSMul
local instance : Module ℝ (E →L[ℂ] E) := Module.restrictScalars ℝ ℂ _
local instance : Algebra ℝ (E →L[ℂ] E) := Algebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ (E →L[ℂ] E) := NormedSpace.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : IsScalarTower ℝ ℂ (E →L[ℂ] E) where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A=(r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A

/-- An onto Hilbert isometry gives a unitary bounded operator. -/
theorem isometry_unitary (W : E →ₗᵢ[ℂ] E) (hs : Function.Surjective W) :
    W.toContinuousLinearMap ∈ unitary (E →L[ℂ] E) := by
  let A := W.toContinuousLinearMap
  have hl : star A*A=1 := W.adjoint_comp_self
  have hr : A*star A=1 := by
    ext v
    obtain ⟨w,rfl⟩ := hs v
    have hh := congrArg (fun B : E →L[ℂ] E => (A*B) w) hl
    change A ((star A) (A w))=A w
    simpa only [mul_assoc,mul_one,mul_apply_eq_comp,one_apply_eq_self] using hh
  exact ⟨hl,hr⟩

/-- The positive polar factor has the same pointwise norm as the original map. -/
theorem sqrt_star_mul_norm (T : E →L[ℂ] E) (v : E) :
    ‖CFC.sqrt (star T*T) v‖=‖T v‖ := by
  let A := CFC.sqrt (star T*T)
  have hp : A.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  have hs : A*A=star T*T := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg T)
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ)]
  congr 1
  calc
    inner ℂ (A v) (A v) = inner ℂ v ((A*A) v) := hp.inner_left_eq_inner_right v (A v)
    _ = inner ℂ v ((star T*T) v) := by rw [hs]
    _ = inner ℂ (T v) (T v) := by
      exact ContinuousLinearMap.adjoint_inner_right T v (T v)

/-- In finite dimension the polar isometry extends to a unitary on the same space. -/
theorem finite_polar [FiniteDimensional ℂ E] (T : E →L[ℂ] E) :
    ∃ W : unitary (E →L[ℂ] E), T=(W : E →L[ℂ] E)*CFC.sqrt (star T*T) := by
  let A := CFC.sqrt (star T*T)
  let f := A.toLinearMap.rangeRestrict
  have hf : Function.Surjective f := LinearMap.surjective_rangeRestrict A.toLinearMap
  have hk : LinearMap.ker f ≤ LinearMap.ker T.toLinearMap := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have ha : A v=0 := congrArg Subtype.val hv
    change T v=0
    apply norm_eq_zero.mp
    rw [← sqrt_star_mul_norm T v]
    change ‖A v‖=0
    rw [ha,norm_zero]
  let g : LinearMap.range A.toLinearMap →ₗ[ℂ] E := f.liftOfSurjective hf ⟨T.toLinearMap,hk⟩
  have hg (v : E) : g (f v)=T v := LinearMap.equivOfSurjective_apply hf hk
  let L : LinearMap.range A.toLinearMap →ₗᵢ[ℂ] E :=
    { toLinearMap := g
      norm_map' := by
        intro v
        obtain ⟨w,rfl⟩ := hf v
        rw [hg]
        exact (sqrt_star_mul_norm T w).symm }
  let W := L.extend
  have hs : Function.Surjective W := LinearMap.surjective_of_injective W.injective
  refine ⟨⟨W.toContinuousLinearMap,isometry_unitary W hs⟩,?_⟩
  ext v
  change T v=W (A v)
  exact (L.extend_apply (f v)).trans (hg v) |>.symm

/-- A finite-dimensional contraction is exactly a mean of two unitaries. -/
theorem finite_mean [FiniteDimensional ℂ E] (T : E →L[ℂ] E) (hT : ‖T‖ ≤ 1) :
    ∃ U V : unitary (E →L[ℂ] E), T=(1/2:ℂ) • ((U : E →L[ℂ] E)+V) := by
  let A := CFC.sqrt (star T*T)
  have hp : A.IsPositive := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg _)
  have hn : ‖A‖ ≤ 1 := by
    apply A.opNorm_le_bound (by norm_num)
    intro v
    change ‖CFC.sqrt (star T*T) v‖ ≤ 1*‖v‖
    rw [sqrt_star_mul_norm]
    exact (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  let C : unitary (E →L[ℂ] E) :=
    ⟨A+Complex.I • CFC.sqrt (1-A^2),
      hp.isSelfAdjoint.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary A hn⟩
  have hc : star (C : E →L[ℂ] E)=A-Complex.I • CFC.sqrt (1-A^2) := by
    change star (A+Complex.I • CFC.sqrt (1-A^2))=_
    have hs : star (CFC.sqrt (1-A^2))=CFC.sqrt (1-A^2) :=
      (CFC.sqrt_nonneg (1-A^2)).isSelfAdjoint.star_eq
    rw [star_add,star_smul,hp.isSelfAdjoint.star_eq,hs]
    simp only [Complex.star_def,Complex.conj_I,neg_smul,sub_eq_add_neg]
  have he : (1/2:ℂ) • ((C : E →L[ℂ] E)+star (C : E →L[ℂ] E))=A := by
    rw [hc]
    change (1/2:ℂ) • ((A+Complex.I • CFC.sqrt (1-A^2))+
      (A-Complex.I • CFC.sqrt (1-A^2)))=A
    module
  obtain ⟨W,hW⟩ := finite_polar T
  refine ⟨W*C,W*star C,?_⟩
  change T=(1/2:ℂ) • ((W : E →L[ℂ] E)*(C : E →L[ℂ] E)+
    (W : E →L[ℂ] E)*star (C : E →L[ℂ] E))
  rw [← mul_add,← mul_smul_comm,he]
  exact hW

#print axioms finite_polar
#print axioms finite_mean
end Sigma2.FiniteContraction


