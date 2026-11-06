import Sigma2.RowCompletenessComplete
import Sigma2.CompilerApproxQutrit
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerCompleteSupport
open Coefficients TensorLifts TraceProducts

/-- An operator killing every covariance column kills the covariance. -/
theorem mul_covariance_zero {ι : Type} (u : ι → H)
    (hu : Summable (fun i => ‖u i‖^2)) (A : Op) (hz : ∀ i,A (u i)=0) :
    A*covariance u=0 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  change inner ℂ w (A (covariance u v))=inner ℂ w 0
  rw [← A.adjoint_inner_left,← (covariance_hasSum u hu (A.adjoint w) v).tsum_eq]
  simp only [A.adjoint_inner_left,hz,inner_zero_right,zero_mul,tsum_zero]

/-- Zero squared density energy implies the actual density annihilator. -/
theorem mul_density_zero_of_energy (h : Density) (A : Op)
    (hz : (trace (h.op*(star A*A))).re=0) : A*h.op=0 := by
  have hB : Positive (star A*A) := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hc := zero_trace_columns h (star A*A) hB hz
  have hcol (k : ℕ) : A (rootFamily h k)=0 := by
    have hi : inner ℂ (A (rootFamily h k)) (A (rootFamily h k))=
        inner ℂ ((star A*A) (rootFamily h k)) (rootFamily h k) := by
      calc
        _=inner ℂ (rootFamily h k) ((star A*A) (rootFamily h k)) :=
          (A.adjoint_inner_right _ _).symm
        _=_ := (hB.isSymmetric _ _).symm
    have hh := hc k
    rw [← hi] at hh
    exact (re_inner_self_nonpos (𝕜 := ℂ)).mp (le_of_eq hh)
  rw [density_eq_covariance]
  exact mul_covariance_zero _ (root_summable h) A hcol

/-- The converse to normal_left_zero, on the original mixed ensemble. -/
theorem mul_marginalA_zero {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalA S h) (A : Op)
    (hz : ∀ k,0<S.weight k → left A (S.vector k)=0) : A*h.op=0 := by
  let u : ℕ × ℕ → H := fun p => column ((Real.sqrt (S.weight p.1):ℂ) • S.vector p.1) p.2
  have hu : Summable (fun p => ‖u p‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun k => (column_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).1,?_⟩
    have he (k : ℕ) : (∑' j,‖u (k,j)‖^2)=S.weight k :=
      (column_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).2.trans
        (weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k))
    simpa only [he] using S.weight_summable
  rw [EntropyComponentBounds.normal_marginalA_covariance S h hm]
  apply mul_covariance_zero u hu A
  intro p
  by_cases hk : 0<S.weight p.1
  · have hh := congrArg (fun v : AB => column v p.2) (hz p.1 hk)
    have h0 : column (0:AB) p.2=0 := by ext i; rfl
    rw [column_left,h0] at hh
    have he : u p=(Real.sqrt (S.weight p.1):ℂ) • column (S.vector p.1) p.2 := by ext i; rfl
    rw [he,map_smul,hh,smul_zero]
  · have hw : S.weight p.1=0 := le_antisymm (le_of_not_gt hk) (S.weight_nonneg _)
    have he : u p=0 := by
      dsimp only [u]
      rw [hw,Real.sqrt_zero,Complex.ofReal_zero,zero_smul]
      ext i
      rfl
    rw [he,map_zero]

theorem mul_marginalB_zero {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalB S h) (A : Op)
    (hz : ∀ k,0<S.weight k → right A (S.vector k)=0) : A*h.op=0 := by
  apply mul_marginalA_zero (PureTransfer.flipNormal S) h hm A
  intro k hk
  change left A (swap (S.vector k))=0
  rw [← PureTransfer.swap_right,hz k hk,map_zero]

#print axioms mul_covariance_zero
#print axioms mul_density_zero_of_energy
#print axioms mul_marginalA_zero
#print axioms mul_marginalB_zero
end Sigma2.CompilerCompleteSupport
