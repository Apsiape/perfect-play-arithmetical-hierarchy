import Sigma2.PureSupport
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.MirrorCentralizer
open Coefficients TensorLifts PureSupport

theorem rankOne_expectation {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (x y : H) :
    inner ℂ S.vector (left (InnerProductSpace.rankOne ℂ x y) S.vector)=inner ℂ y (h.op x) := by
  rw [inner_columns]
  simp only [column_left,InnerProductSpace.inner_right_rankOne_apply]
  rw [marginalA_covariance S h hm]
  calc
    _ = ∑' j,inner ℂ y (column S.vector j)*inner ℂ (column S.vector j) x :=
      tsum_congr (fun _ => mul_comm _ _)
    _ = _ := (covariance_hasSum _ (column_mass S.vector).1 y x).tsum_eq

/-- Self-adjoint mirrors centralize the actual marginal; rank-one tomography
avoids any unproved cyclic trace rule. -/
theorem mirrors_centralize {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (E F : Op) (hE : Positive E) (hF : Positive F)
    (hmatch : left E S.vector=right F S.vector) : Centralizes h.op E := by
  have hL := (left_positive E hE).isSymmetric
  have hR := (right_positive F hF).isSymmetric
  have htrace (K : Op) : inner ℂ S.vector (left (E*K) S.vector)=
      inner ℂ S.vector (left (K*E) S.vector) := by
    rw [left_mul,left_mul]
    change inner ℂ S.vector (left E (left K S.vector))=
      inner ℂ S.vector (left K (left E S.vector))
    calc
      _ = inner ℂ (left E S.vector) (left K S.vector) := (hL _ _).symm
      _ = inner ℂ (right F S.vector) (left K S.vector) := by rw [hmatch]
      _ = inner ℂ S.vector (right F (left K S.vector)) := hR _ _
      _ = inner ℂ S.vector (left K (right F S.vector)) := by
        exact congrArg (fun v : AB => inner ℂ S.vector v)
          (congrArg (fun L : BipOp => L S.vector) (commute K F).symm)
      _ = _ := by rw [← hmatch]
  apply ContinuousLinearMap.ext
  intro x
  change h.op (E x)=E (h.op x)
  apply ext_inner_left ℂ
  intro y
  have hEK : E*InnerProductSpace.rankOne ℂ x y=InnerProductSpace.rankOne ℂ (E x) y := by
    ext v
    simp only [mul_apply_eq_comp,InnerProductSpace.rankOne_apply,map_smul]
  have hKE : InnerProductSpace.rankOne ℂ x y*E=InnerProductSpace.rankOne ℂ x (E y) := by
    apply ContinuousLinearMap.ext
    intro v
    change inner ℂ y (E v) • x=inner ℂ (E y) v • x
    exact congrArg (fun z : ℂ => z • x) (hE.isSymmetric y v).symm
  calc
    _ = inner ℂ S.vector (left (InnerProductSpace.rankOne ℂ (E x) y) S.vector) :=
      (rankOne_expectation S h hm (E x) y).symm
    _ = inner ℂ S.vector (left (E*InnerProductSpace.rankOne ℂ x y) S.vector) := by rw [hEK]
    _ = inner ℂ S.vector (left (InnerProductSpace.rankOne ℂ x y*E) S.vector) := htrace _
    _ = inner ℂ S.vector (left (InnerProductSpace.rankOne ℂ x (E y)) S.vector) := by rw [hKE]
    _ = inner ℂ (E y) (h.op x) := rankOne_expectation S h hm x (E y)
    _ = _ := hE.isSymmetric _ _

#print axioms mirrors_centralize
end Sigma2.MirrorCentralizer
