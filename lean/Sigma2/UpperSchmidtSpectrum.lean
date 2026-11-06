import Sigma2.UpperAnalytic
import Sigma2.UpperAmplitudes

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.UpperSchmidtSpectrum

/-- Contraction of a bipartite vector against an Alice vector. -/
theorem fiber_summable (v : AB) (u : H) :
    Summable (fun j => ‖inner ℂ u (Coefficients.column v j)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ ((Coefficients.column_mass v).1.mul_left (‖u‖^2))
  intro j
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜 := ℂ) u (Coefficients.column v j)) 2

def fiber (v : AB) (u : H) : H :=
  ⟨fun j => inner ℂ u (Coefficients.column v j),memℓp_gen (by simpa using fiber_summable v u)⟩

@[simp] theorem fiber_apply (v : AB) (u : H) (j : ℕ) :
    fiber v u j=inner ℂ u (Coefficients.column v j) := rfl

/-- The reduced density of a unit bipartite vector, in the frozen coordinate model. -/
def density (v : AB) (hv : ‖v‖=1) : Density where
  op := Coefficients.covariance (Coefficients.column v)
  positive := Coefficients.covariance_positive _
  diagonal_summable := (Coefficients.covariance_trace _ (Coefficients.column_mass v).1).1
  trace_one := (Coefficients.covariance_trace _ (Coefficients.column_mass v).1).2.trans
    (by rw [(Coefficients.column_mass v).2,hv,one_pow])

theorem fiber_norm_sq (v : AB) (hv : ‖v‖=1) (u : H) :
    ‖fiber v u‖^2=(inner ℂ u ((density v hv).op u)).re := by
  have hh := (Coefficients.covariance_hasSum (Coefficients.column v) (Coefficients.column_mass v).1 u u).mapL Complex.reCLM
  have he (j : ℕ) :
      (inner ℂ u (Coefficients.column v j)*inner ℂ (Coefficients.column v j) u).re=
        ‖inner ℂ u (Coefficients.column v j)‖^2 := by
    rw [← inner_conj_symm (Coefficients.column v j) u,Complex.mul_conj,
      Complex.ofReal_re,Complex.normSq_eq_norm_sq]
  have hh' : HasSum (fun j => ‖fiber v u j‖^2) (inner ℂ u ((density v hv).op u)).re := by
    simpa only [Complex.reCLM_apply,he,fiber_apply,density] using hh
  exact (Coefficients.norm_sq_hasSum (fiber v u)).unique hh'

/-- The frozen product-overlap sum is exactly the pairing with the contracted vector. -/
theorem product_overlap_fiber (v : AB) (u w : H) :
    productOverlap v u w=inner ℂ w (fiber v u) := by
  have hs : Summable (fun j => ‖(w j) • u‖^2) := by
    simpa only [norm_smul,mul_pow] using (Coefficients.norm_sq_hasSum w).summable.mul_right (‖u‖^2)
  let z : AB := TensorLifts.ofColumns (fun j => (w j) • u) hs
  have hz : productOverlap v u w=inner ℂ z v := by
    apply tsum_congr
    intro ⟨i,j⟩
    simp only [z,TensorLifts.ofColumns_apply,lp.coeFn_smul,Pi.smul_apply,
      smul_eq_mul,RCLike.inner_apply',RCLike.star_def]
    rw [mul_comm (w j) (u i)]
  rw [hz,TensorLifts.inner_columns,lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  simp only [z,TensorLifts.column_ofColumns,inner_smul_left,fiber_apply,RCLike.inner_apply]
  ring

/-- The largest Schmidt probability is the top eigenvalue of the actual reduced density. -/
theorem largest_eq_first (v : AB) (hv : ‖v‖=1)
    (q : ℕ → ℝ) (u : ℕ → H) (hq : ∀ i,0≤q i) (hs : Summable q)
    (ht : (∑' i,q i)=1) (hu : Orthonormal ℂ u) (ha : Antitone q)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) :
    largestSchmidt v=q 0 := by
  have hq0 : 0<q 0 := by
    by_contra hn
    have hz : q=0 := by
      funext i
      exact le_antisymm ((ha (Nat.zero_le i)).trans (not_lt.mp hn)) (hq i)
    simp [hz] at ht
  have hupper (a b : H) (ha1 : ‖a‖=1) (hb1 : ‖b‖=1) :
      ‖productOverlap v a b‖^2≤q 0 := by
    rw [product_overlap_fiber]
    have hn := norm_inner_le_norm (𝕜 := ℂ) b (fiber v a)
    rw [hb1,one_mul] at hn
    have hb := EntropyMinMax.spectral_tail_upper (density v hv) q u hq hs hu he 0 (q 0) (hq 0)
      (fun i _ => ha (Nat.zero_le i)) a (fun i => Fin.elim0 i)
    rw [ha1,one_pow,mul_one,← fiber_norm_sq] at hb
    exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hb
  have hfn : ‖fiber v (u 0)‖^2=q 0 := by
    rw [fiber_norm_sq v hv,EntropyMinMax.apply_spectral_vector (density v hv) q u hu he 0,
      inner_smul_right,inner_self_eq_norm_sq_to_K,hu.norm_eq_one]
    simp
  have hfpos : 0<‖fiber v (u 0)‖ := by nlinarith [norm_nonneg (fiber v (u 0))]
  let w : H := (‖fiber v (u 0)‖⁻¹:ℂ) • fiber v (u 0)
  have hw : ‖w‖=1 := by simp [w,norm_smul,inv_mul_cancel₀ (ne_of_gt hfpos)]
  have hover : ‖productOverlap v (u 0) w‖^2=q 0 := by
    rw [product_overlap_fiber]
    have hpair : ‖inner ℂ w (fiber v (u 0))‖=‖fiber v (u 0)‖ := by
      dsimp only [w]
      rw [inner_smul_left]
      have hc : (starRingEnd ℂ) (‖fiber v (u 0)‖⁻¹:ℂ)=(‖fiber v (u 0)‖⁻¹:ℂ) := by simp
      rw [hc]
      calc
        _ = ‖fiber v (u 0)‖⁻¹*‖fiber v (u 0)‖^2 := by
          simp [norm_mul,inner_self_eq_norm_sq_to_K]
        _ = ‖fiber v (u 0)‖ := by field_simp [ne_of_gt hfpos]
    rw [hpair,hfn]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨‖v (0,0)‖^2,basis 0,basis 0,by simp [basis,lp.norm_single],
        by simp [basis,lp.norm_single],by rw [UpperAnalytic.basis_overlap]⟩
    · rintro p ⟨a,b,ha1,hb1,rfl⟩
      exact hupper a b ha1 hb1
  · apply le_csSup
    · refine ⟨q 0,?_⟩
      rintro p ⟨a,b,ha1,hb1,rfl⟩
      exact hupper a b ha1 hb1
    · exact ⟨u 0,w,hu.norm_eq_one 0,hw,hover.symm⟩

/-- Sorted normalized Schmidt coefficients satisfy the exact stratum budget. -/
theorem normalized_spectrum (v : AB) (hv : ‖v‖=1) (κ : ℕ) (hκpos : 0<κ)
    (hκ : 1/(κ:ℝ)≤largestSchmidt v) :
    ∃ (d q : ℕ → ℝ) (u : ℕ → H),
      d 0=1 ∧ (∀ i,0≤d i) ∧ Antitone d ∧ Summable (fun i => d i^2) ∧
      (∑' i,d i^2)≤κ ∧ Orthonormal ℂ u ∧
      (∀ i,0≤q i) ∧ Summable q ∧ (∑' i,q i)=1 ∧ Antitone q ∧
      (∀ i,d i^2=q i/q 0) ∧ q 0=largestSchmidt v ∧
      (∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) := by
  obtain ⟨q,u,hq,hs,ht,hu,ha,he⟩ := EntropySpectrum.ordered_density_witness (density v hv)
  have htop := largest_eq_first v hv q u hq hs ht hu ha he
  have hq0 : 0<q 0 := htop ▸ UpperAnalytic.largest_pos v hv
  have hk : 0<(κ:ℝ) := by exact_mod_cast hκpos
  let d := fun i => Real.sqrt (q i/q 0)
  have hd2 (i : ℕ) : d i^2=q i/q 0 := Real.sq_sqrt (div_nonneg (hq i) hq0.le)
  have hds : Summable (fun i => d i^2) := by simpa only [hd2] using hs.div_const (q 0)
  have hdb : (∑' i,d i^2)≤κ := by
    simp_rw [hd2]
    rw [tsum_div_const,ht]
    apply (div_le_iff₀ hq0).mpr
    have hh := (div_le_iff₀ hk).mp (show 1/(κ:ℝ)≤q 0 by simpa only [htop] using hκ)
    nlinarith
  refine ⟨d,q,u,?_,(fun i => Real.sqrt_nonneg _),?_,hds,hdb,hu,hq,hs,ht,ha,hd2,htop.symm,he⟩
  · simp only [d,div_self (ne_of_gt hq0),Real.sqrt_one]
  · intro i j hij
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (ha hij) hq0.le)

end Sigma2.UpperSchmidtSpectrum




