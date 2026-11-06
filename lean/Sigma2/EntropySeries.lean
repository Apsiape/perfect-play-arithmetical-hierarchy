import Sigma2.Statements
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000
namespace Sigma2.EntropySeries

/-- Rational Taylor polynomial for the numerator of binary entropy. -/
def raw (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, t*(1-t)^(i+1)/(i+1)

def logTwoPartial (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (1/2:ℝ)^(i+1)/(i+1)

lemma log_tail (N : ℕ) (x : ℝ) (hx : 0≤x) (hx1 : x<1) :
    0 ≤ -Real.log (1-x) - ∑ i ∈ Finset.range N,x^(i+1)/(i+1) ∧
    -Real.log (1-x) - ∑ i ∈ Finset.range N,x^(i+1)/(i+1) ≤
      x^(N+1)/((N+1)*(1-x)) := by
  have hsum := Real.hasSum_pow_div_log_of_abs_lt_one (by rwa [abs_of_nonneg hx])
  have ht : Summable (fun i : ℕ => x^(i+N+1)/(i+N+1)) := by
    simpa only [Nat.cast_add] using (summable_nat_add_iff N).mpr hsum.summable
  have htail : (∑' i : ℕ,x^(i+N+1)/(i+N+1)) =
      -Real.log (1-x) - ∑ i ∈ Finset.range N,x^(i+1)/(i+1) := by
    have h := hsum.summable.sum_add_tsum_nat_add N
    simp only [Nat.cast_add] at h
    rw [hsum.tsum_eq] at h
    linarith only [h]
  have hgeom : HasSum (fun i : ℕ => (x^(N+1)/(N+1))*x^i)
      (x^(N+1)/((N+1)*(1-x))) := by
    have h := (hasSum_geometric_of_lt_one hx hx1).mul_left (x^(N+1)/(N+1))
    convert h using 1
    field_simp
  rw [← htail]
  refine ⟨tsum_nonneg (fun i => by positivity),ht.tsum_le_tsum (fun i => ?_) hgeom.summable |>.trans_eq hgeom.tsum_eq⟩
  calc
    x^(i+N+1)/(i+N+1) ≤ x^(i+N+1)/(N+1) := by
      gcongr
      norm_num
    _ = (x^(N+1)/(N+1))*x^i := by rw [show i+N+1=N+1+i by omega,pow_add]; ring

lemma raw_error (N : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    0 ≤ -t*Real.log t - raw N t ∧
    -t*Real.log t - raw N t ≤ 1/(N+1) := by
  by_cases ht0 : t=0
  · simp [ht0,raw]
    positivity
  have htp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hx : 0≤1-t := by linarith
  have hx1 : 1-t<1 := by linarith
  obtain ⟨ha,hb⟩ := log_tail N (1-t) hx hx1
  have hr : raw N t = t*(∑ i ∈ Finset.range N,(1-t)^(i+1)/(i+1)) := by
    simp only [raw,Finset.mul_sum,mul_div_assoc]
  have hlog : 1-(1-t)=t := by ring
  rw [hlog] at ha hb
  have hcancel : t*((1-t)^(N+1)/((N+1)*t)) = (1-t)^(N+1)/(N+1) := by
    field_simp
  have hp : (1-t)^(N+1) ≤ 1 := pow_le_one₀ hx (by linarith)
  have hb' := mul_le_mul_of_nonneg_left hb ht
  rw [hcancel] at hb'
  rw [hr]
  constructor
  · nlinarith only [mul_nonneg ht ha]
  · have hden : (0:ℝ)<N+1 := by positivity
    have hp' : (1-t)^(N+1)/(N+1) ≤ 1/(N+1) := div_le_div_of_nonneg_right hp hden.le
    nlinarith only [hb',hp']

lemma raw_nonneg (N : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : 0≤raw N t := by
  unfold raw
  exact Finset.sum_nonneg (fun i hi => div_nonneg
    (mul_nonneg ht (pow_nonneg (by linarith) _)) (by positivity))

lemma raw_le_one (N : ℕ) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) : raw N t ≤ 1 := by
  have he := (raw_error N t ht ht1).1
  by_cases ht0 : t=0
  · simp [ht0,raw]
  have htp : 0<t := lt_of_le_of_ne ht (Ne.symm ht0)
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr htp)
  rw [Real.log_inv] at hl
  have hh := mul_le_mul_of_nonneg_left hl ht
  rw [mul_sub,mul_inv_cancel₀ ht0,mul_one] at hh
  linarith

lemma logTwoPartial_lower (N : ℕ) (hN : 0<N) : (1/2:ℝ)≤logTwoPartial N := by
  have hzero : 0 ∈ Finset.range N := Finset.mem_range.mpr hN
  have h := Finset.single_le_sum (f := fun i : ℕ => (1/2:ℝ)^(i+1)/(i+1))
    (fun i hi => by positivity) hzero
  simpa [logTwoPartial] using h

lemma logTwo_lower : (1/2:ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h ⊢
  linarith

lemma logTwoPartial_error (N : ℕ) :
    0 ≤ Real.log 2-logTwoPartial N ∧ Real.log 2-logTwoPartial N ≤ 2/(N+1) := by
  obtain ⟨ha,hb⟩ := raw_error N (1/2) (by norm_num) (by norm_num)
  have hr : raw N (1/2) = (1/2)*logTwoPartial N := by
    simp only [raw,logTwoPartial,Finset.mul_sum,mul_div_assoc]
    norm_num
  rw [hr,Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),Real.log_one,zero_sub] at ha hb
  simp only [div_eq_mul_inv] at ha hb ⊢
  constructor <;> nlinarith

lemma entropy_uniform_error (N : ℕ) (hN : 0<N) (t : ℝ) (ht : 0≤t) (ht1 : t≤1) :
    |raw N t / logTwoPartial N - entropyTerm t| ≤ 10/(N+1) := by
  have hA := logTwoPartial_lower N hN
  have hB := logTwo_lower
  have hp := raw_nonneg N t ht ht1
  have hq := raw_le_one N t ht ht1
  obtain ⟨he0,he⟩ := raw_error N t ht ht1
  obtain ⟨hl0,hl⟩ := logTwoPartial_error N
  have hapos : 0<logTwoPartial N := by linarith
  have hbpos : 0<Real.log 2 := by linarith
  have hnum : 0 ≤ -t*Real.log t := by linarith
  have hn : 0<(N:ℝ)+1 := by positivity
  have hAi : 1/logTwoPartial N ≤ 2 := (div_le_iff₀ hapos).mpr (by linarith)
  have hBi : 1/Real.log 2 ≤ 2 := (div_le_iff₀ hbpos).mpr (by linarith)
  have hInvId : 1/logTwoPartial N-1/Real.log 2 =
      (Real.log 2-logTwoPartial N)*(1/logTwoPartial N)*(1/Real.log 2) := by
    field_simp
    <;> ring
  have hInv0 : 0 ≤ 1/logTwoPartial N-1/Real.log 2 := by rw [hInvId]; positivity
  have hInv : 1/logTwoPartial N-1/Real.log 2 ≤ 8/(N+1) := by
    rw [hInvId]
    calc
      _ ≤ ((2:ℝ)/(N+1))*2*2 := by gcongr
      _ = _ := by ring
  have hfirst0 : 0 ≤ raw N t/logTwoPartial N-raw N t/Real.log 2 := by
    have h := mul_nonneg hp hInv0
    simp only [div_eq_mul_inv,one_mul] at h ⊢
    nlinarith only [h]
  have hfirst : raw N t/logTwoPartial N-raw N t/Real.log 2 ≤ 8/(N+1) := by
    have h := mul_le_mul hq hInv hInv0 (by norm_num : (0:ℝ)≤1)
    simp only [div_eq_mul_inv,one_mul] at h ⊢
    nlinarith only [h]
  have hsecond0 : 0 ≤ (-t*Real.log t-raw N t)/Real.log 2 := div_nonneg he0 hbpos.le
  have hsecond : (-t*Real.log t-raw N t)/Real.log 2 ≤ 2/(N+1) := by
    calc
      _ = (-t*Real.log t-raw N t)*(1/Real.log 2) := by ring
      _ ≤ ((1:ℝ)/(N+1))*2 := mul_le_mul he hBi (by positivity) (by positivity)
      _ = _ := by ring
  rw [sub_div] at hsecond0 hsecond
  unfold entropyTerm
  rw [abs_le]
  simp only [div_eq_mul_inv] at hfirst0 hfirst hsecond0 hsecond ⊢
  constructor <;> nlinarith only [hfirst0,hfirst,hsecond0,hsecond]

#print axioms raw_error
#print axioms entropy_uniform_error
end Sigma2.EntropySeries
