import Sigma2.Reduction

noncomputable section
open scoped BigOperators
namespace Sigma2.Value

def topMass (m : ℕ) : ℝ := 3/((4:ℝ)^(m+1)-1)

def fourRowConstant (Q : ℕ) (L d : Fin 4 → ℕ) : ℝ :=
  (1/(Q:ℝ)^2)*(2/363:ℝ)*∑ a : Fin 4, 4*(L a:ℝ)^2/(d a:ℝ)^3

/-- Eq. (50), normalized top-depth mass and convergence. -/
theorem top_mass_tendsto : Filter.Tendsto topMass Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun m : ℕ => (4:ℝ)^(m+1)) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4)).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hd : Filter.Tendsto (fun m : ℕ => (4:ℝ)^(m+1)-1) Filter.atTop Filter.atTop := by
    simpa only [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right _ (-1:ℝ) hp
  change Filter.Tendsto (fun m => (3:ℝ)/((4:ℝ)^(m+1)-1)) Filter.atTop (nhds 0)
  simpa only [div_eq_mul_inv,Function.comp_def,mul_zero] using
    (tendsto_inv_atTop_zero.comp hd).const_mul (3:ℝ)

end Sigma2.Value

#print axioms Sigma2.Value.top_mass_tendsto


