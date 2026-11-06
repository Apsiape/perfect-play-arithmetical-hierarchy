import Sigma2.FockTruncationStructural

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 400000
namespace Sigma2.FockTruncation
open Sigma2.Tree Sigma2.ReductionFockModel
variable (q : ℕ) [NeZero q]

lemma top_weight_hasSum (m : ℕ) :
    HasSum (fun u : Index q => if u.1.length = m then weight q m u else 0)
      ((3/4:ℝ)*(1/4:ℝ)^m / mass m) := by
  have hn : HasSum (fun n : ℕ => (4:ℝ)^n *
      (if n=m then FockEntropy.probability n else 0)) ((3/4:ℝ)*(1/4:ℝ)^m) := by
    convert (hasSum_ite_eq m ((4:ℝ)^m*FockEntropy.probability m) :
      HasSum (fun n : ℕ => if n=m then (4:ℝ)^m*FockEntropy.probability m else 0)
        ((4:ℝ)^m*FockEntropy.probability m)) using 1
    · funext n
      by_cases h : n=m <;> simp [h]
    · exact (FockEntropy.weighted_probability m).symm
  have hw := FockEntropy.length_hasSum _
    (fun n => by split_ifs; exact (FockEntropy.probability_pos n).le; rfl) _ hn
  have hp := fiber_hasSum q _
    (fun w => by split_ifs; exact (FockEntropy.probability_pos w.length).le; rfl) _ hw
  have hd := hp.div_const (mass m)
  convert hd using 1
  funext u
  by_cases h : u.1.length=m
  · simp [h,weight,ReductionFockWeights.weight,FockEntropy.probability,fockWeight]
  · simp [h]

lemma top_fraction (m : ℕ) :
    (3/4:ℝ)*(1/4:ℝ)^m / mass m = 3 / ((4:ℝ)^(m+1)-1) := by
  have hp : (4:ℝ)^m ≠ 0 := by positivity
  have hbig : 1 < (4:ℝ)^(m+1) := one_lt_pow₀ (by norm_num) (by omega)
  dsimp [mass]
  rw [show (1/4:ℝ)=(4:ℝ)⁻¹ by norm_num,inv_pow,inv_pow,pow_succ]
  field_simp

lemma top_trace (m : ℕ) :
    (trace ((density q m).op * top q m)).re = 3 / ((4:ℝ)^(m+1)-1) := by
  let p : ℕ → ℝ := fun n => if ((enumeration q).symm n).1.length=m then probability q m n else 0
  have hs : HasSum p ((3/4:ℝ)*(1/4:ℝ)^m / mass m) := by
    simpa only [p,probability,Function.comp_def] using
      ((enumeration q).symm.hasSum_iff.mpr (top_weight_hasSum q m))
  have hprob (n : ℕ) : 0 ≤ probability q m n := weight_nonneg q m _
  have hb : FockModel.Bounded (fun n => (p n : ℂ)) := by
    refine ⟨1,fun n => ?_⟩
    dsimp [p]
    split_ifs
    · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hprob n)]
      simpa only [(probability_mass q m).tsum_eq] using
        (probability_mass q m).summable.le_tsum n (fun j hj => hprob j)
    · norm_num
  have hop : (density q m).op * top q m = FockModel.diagonal (fun n => (p n : ℂ)) hb := by
    ext v n
    simp only [density,FockModel.diagonalDensity,mul_apply_eq_comp,top,proj,diag,
      FockModel.diagonal_apply]
    dsimp [p]
    by_cases h : ((enumeration q).symm n).1.length=m <;> simp [h]
  rw [hop,FockModel.diagonal_trace]
  have hc := Complex.ofRealCLM.map_tsum hs.summable
  change (∑' n, Complex.ofRealCLM (p n)).re = _
  rw [← hc]
  change (∑' n,p n) = _
  rw [hs.tsum_eq]
  exact top_fraction m

lemma defect_trace (m : ℕ) (a : Fin 4) :
    (trace ((density q m).op *
      (star (star (creation q m a)*creation q m a-cut q m) *
        (star (creation q m a)*creation q m a-cut q m)))).re =
      3 / ((4:ℝ)^(m+1)-1) := by
  have hs : star (-(top q m)) = -(top q m) := by
    rw [star_neg (top q m),(top_projection q m).1]
  simp only [diagonal_defect]
  rw [hs,neg_mul_neg (top q m) (top q m),(top_projection q m).2]
  exact top_trace q m

#print axioms top_trace
#print axioms defect_trace
end Sigma2.FockTruncation
