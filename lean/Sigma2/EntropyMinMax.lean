import Sigma2.DensitySpectral
import Sigma2.EntropyDomination

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.EntropyMinMax

local instance : SMul ℝ Op := (Module.restrictScalars ℝ ℂ Op).toSMul
local instance : Module ℝ Op := Module.restrictScalars ℝ ℂ Op
local instance : Algebra ℝ Op := Algebra.restrictScalars ℝ ℂ Op
local instance : NormedSpace ℝ Op := NormedSpace.restrictScalars ℝ ℂ Op
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ Op
local instance : IsScalarTower ℝ ℂ Op where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A = (r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A
/-- Domination compares quadratic forms without any commutation assumption. -/
theorem rayleigh_le (h g : Density) (r : ℝ)
    (hd : Positive (h.op - (r : ℂ) • g.op)) (v : H) :
    r * (inner ℂ v (g.op v)).re ≤ (inner ℂ v (h.op v)).re := by
  have hh := hd.re_inner_nonneg_right v
  change 0 ≤ (inner ℂ v (h.op v - (r : ℂ) • g.op v)).re at hh
  simp only [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hh
  linarith

/-- Domination includes the kernel, rather than assuming faithful densities. -/
theorem kernel_inclusion (h g : Density) (r : ℝ) (hr : 0 < r)
    (hd : Positive (h.op - (r : ℂ) • g.op)) (v : H) (hv : h.op v = 0) :
    g.op v = 0 := by
  have hh := rayleigh_le h g r hd v
  have hg : 0 ≤ (inner ℂ v (g.op v)).re := g.positive.re_inner_nonneg_right v
  simp only [hv, inner_zero_right, Complex.zero_re] at hh
  have hz : (inner ℂ v (g.op v)).re = 0 := by nlinarith
  let A := Coefficients.positiveRoot g.op
  have hA : A.IsPositive :=
    ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg g.op)
  have hsq : A*A=g.op :=
    CFC.sqrt_mul_sqrt_self g.op (ContinuousLinearMap.nonneg_iff_isPositive.mpr g.positive)
  have hn : ‖A v‖^2=0 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), hA.inner_left_eq_inner_right]
    change (inner ℂ v ((A*A) v)).re=0
    rw [hsq, hz]
  have hav : A v=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  calc
    g.op v = A (A v) := congrArg (fun T : Op => T v) hsq.symm
    _ = 0 := by rw [hav, map_zero]

/-- Among n+1 independent vectors there is a nonzero vector orthogonal to
any given n vectors. This is the dimension step in the compact min-max proof. -/
theorem exists_orthogonal_combination (n : ℕ) (u : Fin n → H)
    (w : Fin (n+1) → H) (hw : LinearIndependent ℂ w) :
    ∃ v : H, v ≠ 0 ∧ v ∈ Submodule.span ℂ (Set.range w) ∧
      ∀ i, inner ℂ (u i) v = 0 := by
  let W : (Fin (n+1) → ℂ) →ₗ[ℂ] H :=
    { toFun := fun c => ∑ j, c j • w j
      map_add' := by intros; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := by intros; simp [Finset.smul_sum, smul_smul] }
  let F : (Fin (n+1) → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    LinearMap.pi (fun i => (innerSL ℂ (u i)).toLinearMap.comp W)
  have hk : LinearMap.ker F ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simp)
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨W c, ?_, ?_, ?_⟩
  · intro hz
    apply hc0
    have h := (linearIndependent_iff'.mp hw) Finset.univ c hz
    funext j
    exact h j (Finset.mem_univ j)
  · change (∑ j, c j • w j) ∈ Submodule.span ℂ (Set.range w)
    exact Submodule.sum_mem _ (fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j)))
  · intro i
    exact congrFun hc i

/-- The variational comparison step, valid also for infinite-rank densities.
The two trial families need not be orthogonal to one another. -/
theorem minmax_bound (h g : Density) (r a b : ℝ) (hr : 0 < r)
    (hd : Positive (h.op - (r : ℂ) • g.op)) (n : ℕ)
    (u : Fin n → H) (w : Fin (n+1) → H) (hw : LinearIndependent ℂ w)
    (hupper : ∀ v : H, (∀ i, inner ℂ (u i) v = 0) →
      (inner ℂ v (h.op v)).re ≤ a * ‖v‖^2)
    (hlower : ∀ v ∈ Submodule.span ℂ (Set.range w),
      b * ‖v‖^2 ≤ (inner ℂ v (g.op v)).re) :
    r*b ≤ a := by
  obtain ⟨v, hv, hspan, horth⟩ := exists_orthogonal_combination n u w hw
  have hn : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have he := rayleigh_le h g r hd v
  have hu := hupper v horth
  have hl := mul_le_mul_of_nonneg_left (hlower v hspan) hr.le
  nlinarith

#print axioms rayleigh_le
#print axioms kernel_inclusion
#print axioms exists_orthogonal_combination
#print axioms minmax_bound
end Sigma2.EntropyMinMax




