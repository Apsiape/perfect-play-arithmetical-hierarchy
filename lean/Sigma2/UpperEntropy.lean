import Sigma2.Preliminaries

noncomputable section
open scoped BigOperators
namespace Sigma2.UpperEntropy
set_option maxHeartbeats 200000

theorem sorted_probability_bound (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    (ht : (∑' i,p i)=1) (hd : Antitone p) (n : ℕ) : p n ≤ 1/(n+1) := by
  have hsum : (n+1:ℝ)*p n ≤ 1 := by
    calc
      _ = ∑ i ∈ Finset.range (n+1), p n := by simp
      _ ≤ ∑ i ∈ Finset.range (n+1), p i := Finset.sum_le_sum fun i hi =>
        hd (by simpa using Finset.mem_range.mp hi)
      _ ≤ ∑' i,p i := hs.sum_le_tsum _ (fun i _ => hp i)
      _ = 1 := ht
  exact (le_div_iff₀ (by positivity : (0:ℝ)<n+1)).mpr (by nlinarith)

theorem tail (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    (ht : (∑' i, p i)=1) (hd : Antitone p)
    (hH : Summable (fun i => entropyTerm (p i))) (B : ℝ)
    (hB : (∑' i, entropyTerm (p i)) ≤ B) (n : ℕ) :
    (∑' i, p (i+n+1)) ≤ B / (Real.log (n+2) / Real.log 2) := by
  have hlog2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hlogn : 0<Real.log (n+2) := Real.log_pos (by have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hden : (0:ℝ)<n+2 := by positivity
  have hp1 i : p i ≤ 1 := by
    exact (hs.le_tsum i (fun j _ => hp j)).trans_eq ht
  have hent i : 0 ≤ entropyTerm (p i) := EntropyDomination.entropy_nonneg (hp i) (hp1 i)
  have hpoint i : p (i+n+1)*(Real.log (n+2)/Real.log 2) ≤ entropyTerm (p (i+n+1)) := by
    have hq : p (i+n+1) ≤ 1/(n+2) := by
      exact (hd (by omega : n+1 ≤ i+n+1)).trans (by simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using sorted_probability_bound p hp hs ht hd (n+1))
    by_cases hz : p (i+n+1)=0
    · simp [hz,entropyTerm]
    have hpos : 0<p (i+n+1) := lt_of_le_of_ne (hp _) (Ne.symm hz)
    have hl := Real.log_le_log hpos hq
    rw [Real.log_div one_ne_zero (ne_of_gt hden), Real.log_one, zero_sub] at hl
    unfold entropyTerm
    apply (le_div_iff₀ hlog2).mpr
    have hm := mul_le_mul_of_nonneg_left hl (hp (i+n+1))
    field_simp
    nlinarith
  have hps : Summable (fun i => p (i+n+1)) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (f := p) (n+1)).mpr hs
  have hHs : Summable (fun i => entropyTerm (p (i+n+1))) := by
    simpa only [Nat.add_assoc] using (summable_nat_add_iff (f := fun i => entropyTerm (p i)) (n+1)).mpr hH
  have htH : (∑' i,entropyTerm (p (i+n+1))) ≤ ∑' i,entropyTerm (p i) := by
    exact tsum_comp_le_tsum_of_inj (i := fun i : ℕ => i+n+1) hH hent
      (by intro i j h; exact Nat.add_right_cancel (Nat.add_right_cancel h))
  apply (le_div_iff₀ (div_pos hlogn hlog2)).mpr
  calc
    _ = ∑' i,p (i+n+1)*(Real.log (n+2)/Real.log 2) := (tsum_mul_right).symm
    _ ≤ ∑' i,entropyTerm (p (i+n+1)) := (hps.mul_right _).tsum_le_tsum hpoint hHs
    _ ≤ ∑' i,entropyTerm (p i) := htH
    _ ≤ B := hB

end Sigma2.UpperEntropy
