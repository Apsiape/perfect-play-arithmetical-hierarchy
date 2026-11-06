import Sigma2.NormalCoefficients
import Sigma2.EntropyDomination

noncomputable section
set_option maxHeartbeats 300000
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.EntropyComponentBounds
open Coefficients

/-- Operator equality can be checked on the canonical matrix coefficients. -/
private theorem op_ext (A B : Op) (h : ∀ i j, entry A i j = entry B i j) : A = B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro c
  change A (lp.single 2 j c) = B (lp.single 2 j c)
  have hc : lp.single 2 j c = c • basis j := by simp [basis, ← lp.single_smul]
  rw [hc, map_smul, map_smul]
  congr 1
  ext i
  exact h i j


/-- Scaling a nuclear covariance by a nonnegative scalar. -/
theorem covariance_scale (u : ℕ → H) (hu : Summable (fun j => ‖u j‖^2))
    (r : ℝ) (hr : 0≤r) :
    covariance (fun j => (Real.sqrt r:ℂ) • u j)=(r:ℂ) • covariance u := by
  have hs : Summable (fun j => ‖(Real.sqrt r:ℂ) • u j‖^2) := by
    simp_rw [norm_smul,mul_pow]
    exact hu.mul_left _
  apply op_ext
  intro a b
  change covariance (fun j => (Real.sqrt r:ℂ) • u j) (basis b) a=
    (r:ℂ)*(covariance u (basis b) a)
  rw [show basis b=lp.single 2 b 1 from rfl,covariance_entry _ hs,covariance_entry _ hu]
  simp_rw [weighted_entry r hr,tsum_mul_left]

#print axioms covariance_scale

/-- A whole ensemble covariance dominates each of its grouped components. -/
theorem covariance_fiber_le (u : ℕ × ℕ → H)
    (hu : Summable (fun p => ‖u p‖^2)) (k : ℕ) :
    (covariance u-covariance (fun j => u (k,j))).IsPositive := by
  have hs := summable_rankOne u hu
  have ht : Summable (fun i => covariance (fun j => u (i,j))) := hs.prod
  have he : covariance u=∑' i,covariance (fun j => u (i,j)) := hs.tsum_prod
  have hh : covariance (fun j => u (k,j))≤covariance u := by
    rw [he]
    exact ht.le_tsum k (fun i _ =>
      ContinuousLinearMap.nonneg_iff_isPositive.mpr (covariance_positive _))
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp (sub_nonneg.mpr hh)


#print axioms covariance_fiber_le

/-- The original A marginal is its weighted coefficient covariance. -/
theorem normal_marginalA_covariance {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalA S h) :
    h.op=covariance (fun p : ℕ × ℕ => column ((Real.sqrt (S.weight p.1):ℂ) • S.vector p.1) p.2) := by
  let u : ℕ × ℕ → H := fun p => column ((Real.sqrt (S.weight p.1):ℂ) • S.vector p.1) p.2
  have hu : Summable (fun p => ‖u p‖^2) := by
    have hf (k : ℕ) : Summable (fun j => ‖u (k,j)‖^2) :=
      (column_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).1
    have he (k : ℕ) : (∑' j,‖u (k,j)‖^2)=S.weight k :=
      (column_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).2.trans
        (weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k))
    exact (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
      ⟨hf,by simpa only [he] using S.weight_summable⟩
  apply op_ext
  intro i j
  rw [hm i j]
  change _=covariance u (basis j) i
  rw [show basis j=lp.single 2 j 1 from rfl,covariance_entry u hu,
    (coefficient_summable u hu i j).tsum_prod]
  apply tsum_congr
  intro k
  simp only [u,column_apply]
  simp_rw [weighted_entry _ (S.weight_nonneg k),tsum_mul_left]

/-- A component marginal is dominated by its original ensemble marginal. -/
theorem component_marginalA_dominated {s} (S : NormalStrategy s) (k : ℕ) (h g : Density)
    (hm : MarginalA S h) (hg : MarginalA (normalOfPure (S.component k)) g) :
    (h.op-(S.weight k:ℂ) • g.op).IsPositive := by
  let u : ℕ × ℕ → H := fun p => column ((Real.sqrt (S.weight p.1):ℂ) • S.vector p.1) p.2
  have hu : Summable (fun p => ‖u p‖^2) := by
    have hf (k : ℕ) : Summable (fun j => ‖u (k,j)‖^2) :=
      (column_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).1
    have he (k : ℕ) : (∑' j,‖u (k,j)‖^2)=S.weight k :=
      (column_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).2.trans
        (weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k))
    exact (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
      ⟨hf,by simpa only [he] using S.weight_summable⟩
  have he : g.op=covariance (fun j => column (S.vector k) j) := by
    apply op_ext
    intro i j
    rw [hg i j]
    change _=covariance (fun j => column (S.vector k) j) (basis j) i
    rw [show basis j=lp.single 2 j 1 from rfl,covariance_entry _ (column_mass _).1]
    have hw (n : ℕ) : ((if n=0 then 1 else 0 : ℝ):ℂ)=if n=0 then 1 else 0 := by
      split_ifs <;> rfl
    simp [normalOfPure,NormalStrategy.component,column_apply,hw,ite_mul]
  have hs (j : ℕ) : u (k,j)=(Real.sqrt (S.weight k):ℂ) • column (S.vector k) j := by
    ext i
    rfl
  rw [normal_marginalA_covariance S h hm,he]
  have hh := covariance_fiber_le u hu k
  simp_rw [hs,covariance_scale _ (column_mass _).1 _ (S.weight_nonneg k)] at hh
  exact hh

/-- The original B marginal is its weighted coefficient covariance. -/
theorem normal_marginalB_covariance {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalB S h) :
    h.op=covariance (fun p : ℕ × ℕ => row ((Real.sqrt (S.weight p.1):ℂ) • S.vector p.1) p.2) := by
  let u : ℕ × ℕ → H := fun p => row ((Real.sqrt (S.weight p.1):ℂ) • S.vector p.1) p.2
  have hu : Summable (fun p => ‖u p‖^2) := by
    have hf (k : ℕ) : Summable (fun j => ‖u (k,j)‖^2) :=
      (row_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).1
    have he (k : ℕ) : (∑' j,‖u (k,j)‖^2)=S.weight k :=
      (row_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).2.trans
        (weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k))
    exact (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
      ⟨hf,by simpa only [he] using S.weight_summable⟩
  apply op_ext
  intro i j
  rw [hm i j]
  change _=covariance u (basis j) i
  rw [show basis j=lp.single 2 j 1 from rfl,covariance_entry u hu,
    (coefficient_summable u hu i j).tsum_prod]
  apply tsum_congr
  intro k
  simp only [u,row_apply]
  simp_rw [weighted_entry _ (S.weight_nonneg k),tsum_mul_left]

/-- A component marginal is dominated by its original ensemble marginal. -/
theorem component_marginalB_dominated {s} (S : NormalStrategy s) (k : ℕ) (h g : Density)
    (hm : MarginalB S h) (hg : MarginalB (normalOfPure (S.component k)) g) :
    (h.op-(S.weight k:ℂ) • g.op).IsPositive := by
  let u : ℕ × ℕ → H := fun p => row ((Real.sqrt (S.weight p.1):ℂ) • S.vector p.1) p.2
  have hu : Summable (fun p => ‖u p‖^2) := by
    have hf (k : ℕ) : Summable (fun j => ‖u (k,j)‖^2) :=
      (row_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).1
    have he (k : ℕ) : (∑' j,‖u (k,j)‖^2)=S.weight k :=
      (row_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).2.trans
        (weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k))
    exact (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
      ⟨hf,by simpa only [he] using S.weight_summable⟩
  have he : g.op=covariance (fun j => row (S.vector k) j) := by
    apply op_ext
    intro i j
    rw [hg i j]
    change _=covariance (fun j => row (S.vector k) j) (basis j) i
    rw [show basis j=lp.single 2 j 1 from rfl,covariance_entry _ (row_mass _).1]
    have hw (n : ℕ) : ((if n=0 then 1 else 0 : ℝ):ℂ)=if n=0 then 1 else 0 := by
      split_ifs <;> rfl
    simp [normalOfPure,NormalStrategy.component,row_apply,hw,ite_mul]
  have hs (j : ℕ) : u (k,j)=(Real.sqrt (S.weight k):ℂ) • row (S.vector k) j := by
    ext i
    rfl
  rw [normal_marginalB_covariance S h hm,he]
  have hh := covariance_fiber_le u hu k
  simp_rw [hs,covariance_scale _ (row_mass _).1 _ (S.weight_nonneg k)] at hh
  exact hh


end Sigma2.EntropyComponentBounds
