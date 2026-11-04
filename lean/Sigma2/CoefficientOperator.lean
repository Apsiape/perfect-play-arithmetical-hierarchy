import Sigma2.MirrorAlgebra

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CoefficientOperator
open Coefficients TensorLifts PureSupport Preliminaries

/-- The coefficient map uses the original Bob coordinates, without removing
its kernel or changing the tensor cut. -/
def vector (v : AB) (x : H) : H :=
  ⟨fun i => inner ℂ (star (row v i)) x, memℓp_gen (by
    simp only [ENNReal.toReal_ofNat,Real.rpow_two]
    apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun i => ?_)
      ((row_mass v).1.mul_right (‖x‖^2))
    calc
      ‖inner ℂ (star (row v i)) x‖^2 ≤ (‖star (row v i)‖*‖x‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) _ _) 2
      _ = ‖row v i‖^2*‖x‖^2 := by rw [norm_star,mul_pow])⟩

theorem vector_bound (v : AB) (x : H) : ‖vector v x‖ ≤ ‖v‖*‖x‖ := by
  have hh : ‖vector v x‖^2 ≤ (‖v‖*‖x‖)^2 := by
    rw [← (norm_sq_hasSum (vector v x)).tsum_eq]
    calc
      _ ≤ ∑' i, ‖row v i‖^2*‖x‖^2 :=
        (norm_sq_hasSum (vector v x)).summable.tsum_le_tsum
          (fun i => by
            change ‖inner ℂ (star (row v i)) x‖^2 ≤ _
            simpa only [norm_star,mul_pow] using
              pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) (star (row v i)) x) 2)
          ((row_mass v).1.mul_right (‖x‖^2))
      _ = _ := by rw [tsum_mul_right,(row_mass v).2,mul_pow]
  nlinarith [norm_nonneg (vector v x),mul_nonneg (norm_nonneg v) (norm_nonneg x)]

def coefficient (v : AB) : Op :=
  LinearMap.mkContinuous
    { toFun := vector v
      map_add' := by intro x y; ext i; exact inner_add_right _ _ _
      map_smul' := by intro c x; ext i; exact inner_smul_right _ _ _ }
    ‖v‖ (vector_bound v)

@[simp] theorem coefficient_apply (v : AB) (x : H) (i : ℕ) :
    coefficient v x i=inner ℂ (star (row v i)) x := rfl

@[simp] theorem coefficient_basis (v : AB) (j : ℕ) :
    coefficient v (basis j)=column v j := by
  ext i
  simp [coefficient_apply,basis,lp.inner_single_right,lp.star_apply,
    RCLike.inner_apply,RCLike.star_def]

theorem coefficient_injective : Function.Injective coefficient := by
  intro v w h
  ext ⟨i,j⟩
  simpa only [coefficient_basis,column_apply] using congrArg (fun T : Op => T (basis j) i) h

theorem adjoint_apply (v : AB) (x : H) (j : ℕ) :
    star (coefficient v) x j=inner ℂ (column v j) x := by
  have hh := (coefficient v).adjoint_inner_right (basis j) x
  change inner ℂ (basis j) (star (coefficient v) x)=inner ℂ (coefficient v (basis j)) x at hh
  rw [coefficient_basis] at hh
  simpa [basis,lp.inner_single_left,RCLike.inner_apply] using hh

/-- N2: the product with the adjoint is the actual (unnormalized) marginal. -/
theorem coefficient_covariance (v : AB) :
    coefficient v*star (coefficient v)=covariance (column v) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  change inner ℂ x (coefficient v (star (coefficient v) y))=_
  rw [← (coefficient v).adjoint_inner_left]
  change inner ℂ (star (coefficient v) x) (star (coefficient v) y)=_
  rw [lp.inner_eq_tsum,← (covariance_hasSum _ (column_mass v).1 x y).tsum_eq]
  apply tsum_congr
  intro j
  simp only [adjoint_apply,RCLike.inner_apply]
  rw [inner_conj_symm x (column v j)]
  exact mul_comm (inner ℂ (column v j) y) (inner ℂ x (column v j))

theorem coefficient_marginal {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) :
    coefficient S.vector*star (coefficient S.vector)=h.op :=
  (coefficient_covariance _).trans (marginalA_covariance S h hm).symm

theorem coefficient_left (v : AB) (A : Op) :
    coefficient (left A v)=A*coefficient v := by
  apply op_ext
  intro i j
  simp only [entry,coefficient_basis,mul_apply_eq_comp,column_left]

/-- The transpose in the fixed original local basis. -/
def transpose (A : Op) : Op :=
  LinearMap.mkContinuous
    { toFun := fun x => star (star A (star x))
      map_add' := by intro x y; simp only [star_add,map_add]
      map_smul' := by
        intro c x
        simp only [star_smul,map_smul,star_star,RingHom.id_apply] }
    ‖A‖ (by
      intro x
      change ‖star (star A (star x))‖ ≤ ‖A‖*‖x‖
      have hn : ‖star A‖=‖A‖ := ContinuousLinearMap.adjoint.norm_map A
      simpa only [norm_star,hn] using (star A).le_opNorm (star x))

theorem transpose_entry (A : Op) (i j : ℕ) : entry (transpose A) i j=entry A j i := by
  have hb : star (basis j)=basis j := by
    ext k
    by_cases hk : k=j <;> simp [basis,lp.star_apply,lp.single_apply,Pi.single_apply,hk]
  have hh := A.adjoint_inner_right (basis i) (basis j)
  change inner ℂ (basis i) (star A (basis j))=inner ℂ (A (basis i)) (basis j) at hh
  simp only [basis,lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply,
    one_mul,map_one,mul_one] at hh
  change star (star A (star (basis j)) i)=_
  rw [hb]
  exact (congrArg star hh).trans (star_star _)

theorem coefficient_right (v : AB) (B : Op) :
    coefficient (right B v)=coefficient v*transpose B := by
  apply op_ext
  intro i j
  change coefficient (right B v) (basis j) i=coefficient v (transpose B (basis j)) i
  rw [coefficient_basis,column_apply,operator_coordinates,right_apply,operator_coordinates]
  apply tsum_congr
  intro k
  rw [show entry (coefficient v) i k=v (i,k) by simp [entry],
    show transpose B (basis j) k=entry B j k from transpose_entry B k j]
  exact mul_comm _ _

theorem mirror_iff (v : AB) (A B : Op) :
    left A v=right B v ↔ A*coefficient v=coefficient v*transpose B := by
  rw [← coefficient_left,← coefficient_right]
  exact ⟨congrArg coefficient,fun hh => coefficient_injective hh⟩

/-- N3 on the original marginal support, including coefficient maps with kernel. -/
theorem coefficient_cancel {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (A : Op) (hz : A*coefficient S.vector=0) : A*P=0 := by
  apply columns_zero_support S h hm P hP A
  intro j
  have hh := congrArg (fun T : Op => T (basis j)) hz
  simpa only [mul_apply_eq_comp,coefficient_basis,zero_apply] using hh

#print axioms coefficient_marginal
#print axioms mirror_iff
#print axioms coefficient_cancel
end Sigma2.CoefficientOperator
