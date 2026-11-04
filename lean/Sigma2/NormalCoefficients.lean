import Sigma2.Coefficients
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.Coefficients
variable {κ ι : Type}

/-- Restrict an lp vector to any injectively indexed set of coordinates. -/
def restrict (f : ι ↪ κ) (v : Space κ) : Space ι :=
  ⟨fun i => v (f i), memℓp_gen (by
    simpa [Function.comp_def] using (norm_sq_hasSum v).summable.comp_injective f.injective)⟩

@[simp] theorem restrict_apply (f : ι ↪ κ) (v : Space κ) (i : ι) :
    restrict f v i = v (f i) := rfl

/-- Columns and rows are genuine vectors in the fixed local Hilbert space. -/
def column (v : AB) (b : ℕ) : H := restrict ⟨fun a => (a,b), fun _ _ h => congrArg Prod.fst h⟩ v
def row (v : AB) (a : ℕ) : H := restrict ⟨fun b => (a,b), fun _ _ h => congrArg Prod.snd h⟩ v

@[simp] theorem column_apply (v : AB) (b a : ℕ) : column v b a=v (a,b) := rfl
@[simp] theorem row_apply (v : AB) (a b : ℕ) : row v a b=v (a,b) := rfl

theorem column_mass (v : AB) :
    Summable (fun b => ‖column v b‖^2) ∧ (∑' b, ‖column v b‖^2)=‖v‖^2 := by
  have hs := (norm_sq_hasSum v).summable
  have he b : ‖column v b‖^2=∑' a, ‖v (a,b)‖^2 := (norm_sq_hasSum (column v b)).tsum_eq.symm
  simp_rw [he]
  exact ⟨hs.prod_symm.prod, (hs.tsum_comm).trans (hs.tsum_prod.symm.trans (norm_sq_hasSum v).tsum_eq)⟩

theorem row_mass (v : AB) :
    Summable (fun a => ‖row v a‖^2) ∧ (∑' a, ‖row v a‖^2)=‖v‖^2 := by
  have hs := (norm_sq_hasSum v).summable
  have he a : ‖row v a‖^2=∑' b, ‖v (a,b)‖^2 := (norm_sq_hasSum (row v a)).tsum_eq.symm
  simp_rw [he]
  exact ⟨hs.prod, hs.tsum_prod.symm.trans (norm_sq_hasSum v).tsum_eq⟩

open scoped Classical in
def unitVector [Nonempty κ] (v : Space κ) : Space κ :=
  if v=0 then lp.single 2 (Classical.arbitrary κ) 1 else ((‖v‖⁻¹:ℝ):ℂ) • v

theorem unitVector_unit [Nonempty κ] (v : Space κ) : ‖unitVector v‖=1 := by
  classical
  by_cases hv : v=0
  · simp [unitVector,hv,lp.norm_single]
  · simp [unitVector,hv,norm_smul]

theorem unitVector_coefficient [Nonempty κ] (u v w : Space κ) :
    ((‖u‖^2:ℝ):ℂ)*inner ℂ v (unitVector u)*inner ℂ (unitVector u) w =
      inner ℂ v u*inner ℂ u w := by
  classical
  by_cases hu : u=0
  · simp [hu]
  · let c : ℂ := ((‖u‖⁻¹:ℝ):ℂ)
    have he : unitVector u=c • u := by simp only [unitVector,ite_eq_right hu]; rfl
    rw [he,inner_smul_right,inner_smul_left]
    have hc : (starRingEnd ℂ) c=c := Complex.conj_ofReal (‖u‖⁻¹:ℝ)
    rw [hc]
    dsimp only [c]
    rw [Complex.ofReal_inv,Complex.ofReal_pow]
    have hn : (‖u‖:ℂ)≠0 := by exact_mod_cast norm_ne_zero_iff.mpr hu
    field_simp [hn]

theorem weighted_unit_norm (r : ℝ) (hr : 0≤r) (v : Space κ) (hv : ‖v‖=1) :
    ‖(Real.sqrt r:ℂ) • v‖^2 = r := by
  rw [norm_smul,hv,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hr]

theorem weighted_coefficient (r : ℝ) (hr : 0≤r) (u v w : Space κ) :
    inner ℂ v ((Real.sqrt r:ℂ) • u)*inner ℂ ((Real.sqrt r:ℂ) • u) w =
      (r:ℂ)*inner ℂ v u*inner ℂ u w := by
  simp only [inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  have hh : (Real.sqrt r:ℂ)*(Real.sqrt r:ℂ)=(r:ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hr
  calc
    _ = ((Real.sqrt r:ℂ)*(Real.sqrt r:ℂ))*(inner ℂ v u*inner ℂ u w) := by ring
    _ = _ := by rw [hh]; ring


open scoped Classical in
theorem coefficient_summable [DecidableEq κ] (u : ι → Space κ) (hu : Summable (fun i => ‖u i‖^2)) (a b : κ) :
    Summable (fun i => u i a * star (u i b)) := by
  have hh := (covariance_hasSum u hu (lp.single 2 a 1) (lp.single 2 b 1)).summable
  simpa [lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply,mul_comm] using hh

open scoped Classical in
theorem weighted_entry [DecidableEq κ] (r : ℝ) (hr : 0≤r) (u : Space κ) (a b : κ) :
    ((r.sqrt:ℂ) • u) a * star (((r.sqrt:ℂ) • u) b) = (r:ℂ)*(u a*star (u b)) := by
  have hh := weighted_coefficient r hr u (lp.single 2 a 1) (lp.single 2 b 1)
  simpa [lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply,mul_comm,mul_assoc] using hh


/-- The covariance kernel is exactly the orthogonal complement of the coefficient family. -/
theorem covariance_kernel (u : ι → Space κ) (hu : Summable (fun i => ‖u i‖^2)) (v : Space κ) :
    covariance u v=0 ↔ ∀ i,inner ℂ v (u i)=0 := by
  constructor
  · intro hz
    have hh := (covariance_hasSum u hu v v).mapL Complex.reCLM
    have hs : HasSum (fun i => ‖inner ℂ v (u i)‖^2) (0:ℝ) := by
      convert hh using 1
      · funext i
        have hc : inner ℂ (u i) v=star (inner ℂ v (u i)) := (inner_conj_symm (u i) v).symm
        change ‖inner ℂ v (u i)‖^2 = (inner ℂ v (u i)*inner ℂ (u i) v).re
        rw [hc,RCLike.star_def,RCLike.mul_conj]
        norm_cast
      · simp [hz]
    have hzero := (hasSum_zero_iff_of_nonneg (fun i => sq_nonneg (‖inner ℂ v (u i)‖))).mp hs
    intro i
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp (congrFun hzero i))
  · intro hz
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [← (covariance_hasSum u hu (covariance u v) v).tsum_eq]
    have he (i : ι) : inner ℂ (u i) v=0 := by rw [← inner_conj_symm (u i) v,hz i]; simp
    simp only [he,mul_zero,tsum_zero]

#print axioms column_mass
#print axioms unitVector_coefficient
#print axioms coefficient_summable
#print axioms covariance_kernel
end Sigma2.Coefficients

