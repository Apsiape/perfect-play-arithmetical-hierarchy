import Sigma2.CoefficientOperator
import Sigma2.CompilerBase

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CoefficientOperator
open Coefficients TensorLifts PureSupport

theorem adjoint_entry (A : Op) (i j : ℕ) : entry (star A) i j=star (entry A j i) := by
  have hh := A.adjoint_inner_right (basis i) (basis j)
  change inner ℂ (basis i) (star A (basis j))=inner ℂ (A (basis i)) (basis j) at hh
  simpa [basis,entry,lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply,RCLike.star_def] using hh

theorem transpose_star (A : Op) : star (transpose A)=transpose (star A) := by
  apply op_ext
  intro i j
  rw [adjoint_entry,transpose_entry,transpose_entry,adjoint_entry]

/-- N4c for any vector, with no normalization or positivity assumption on the
two self-adjoint mirrored operators. -/
theorem mirrors_covariance (v : AB) (X Y : Op) (hX : star X=X) (hY : star Y=Y)
    (hm : left X v=right Y v) :
    X*covariance (column v)=covariance (column v)*X := by
  have ht : star (transpose Y)=transpose Y := by rw [transpose_star,hY]
  rw [← coefficient_covariance]
  exact Compiler.calibrated_density_commutes X (transpose Y) (coefficient v) hX ht ((mirror_iff v X Y).mp hm)

#print axioms mirrors_covariance
end Sigma2.CoefficientOperator
