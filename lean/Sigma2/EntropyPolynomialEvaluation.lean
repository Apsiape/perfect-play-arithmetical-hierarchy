import Sigma2.EntropyPolynomial

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000
namespace Sigma2.EntropyPolynomial

lemma sum_map_range {α : Type} [AddCommMonoid α] (N : ℕ) (f : ℕ → α) :
    ((List.range N).map f).sum = ∑ i ∈ Finset.range N,f i := by
  induction N with
  | zero => simp
  | succ N ih => simp [List.range_succ,Finset.sum_range_succ,ih]

lemma cast_list_sum (l : List ℕ) : ((l.sum : ℕ) : ℝ) = (l.map (fun n => (n:ℝ))).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma factorial_div_cast (N j : ℕ) (hj : 0<j) (hjN : j≤N) :
    ((N.factorial/j : ℕ) : ℝ) = (N.factorial:ℝ)/j :=
  Nat.cast_div (Nat.dvd_factorial hj hjN) (by exact_mod_cast hj.ne')

lemma scale_pos (N : ℕ) : 0<scale N := by unfold scale; positivity

lemma logNumerator_pos (N : ℕ) (hN : 0<N) : 0<logNumerator N := by
  unfold logNumerator
  rw [sum_map_range]
  have h := Finset.single_le_sum (f := fun i => (N.factorial/(i+1))*2^(N-(i+1)))
    (fun i hi => Nat.zero_le _) (Finset.mem_range.mpr hN)
  simp only [Nat.zero_add,Nat.div_one] at h
  exact lt_of_lt_of_le (by positivity) h

lemma denominator_pos (N : ℕ) (hN : 0<N) : 0<denominator N :=
  Nat.mul_pos (Nat.factorial_pos _) (logNumerator_pos N hN)

lemma logNumerator_real (N : ℕ) :
    (logNumerator N : ℝ) = (scale N : ℝ) * EntropySeries.logTwoPartial N := by
  have he : logNumerator N = ∑ i ∈ Finset.range N,(N.factorial/(i+1))*2^(N-(i+1)) := by
    unfold logNumerator
    rw [sum_map_range]
  rw [he,Nat.cast_sum]
  unfold scale EntropySeries.logTwoPartial
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hiN : i+1≤N := by have := Finset.mem_range.mp hi; omega
  rw [factorial_div_cast N (i+1) (by omega) hiN]
  have hp : (2:ℝ)^N = (2:ℝ)^(N-(i+1))*(2:ℝ)^(i+1) := by
    rw [← pow_add,Nat.sub_add_cancel hiN]
  rw [hp,div_pow]
  norm_num
  field_simp

lemma binomial (N j : ℕ) (hj : j≤N) (t : ℝ) :
    (∑ h ∈ Finset.range (N+1),(-1:ℝ)^h*(j.choose h:ℝ)*t^h)=(1-t)^j := by
  have he : (∑ h ∈ Finset.range (j+1),(-1:ℝ)^h*(j.choose h:ℝ)*t^h) =
      ∑ h ∈ Finset.range (N+1),(-1:ℝ)^h*(j.choose h:ℝ)*t^h := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro h hh hnot
    have hlt : j<h := by simp only [Finset.mem_range] at hh hnot; omega
    simp [Nat.choose_eq_zero_of_lt hlt]
  rw [← he]
  have h := add_pow (-t) (1:ℝ) j
  have hre : -t+1=1-t := by ring
  rw [hre] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow,mul_one,show -t=(-1:ℝ)*t by ring,mul_pow]
  ring

lemma signed_real (h a : ℕ) : (signed h a : ℝ) = (-1:ℝ)^h*(a:ℝ) := by
  unfold signed
  by_cases he : h%2=0
  · have hpow : (-1:ℝ)^h=1 := (even_iff_two_dvd.mpr (Nat.dvd_of_mod_eq_zero he)).neg_one_pow
    simp [he,hpow]
  · have hodd : Odd h := Nat.odd_iff.mpr (by omega)
    simp [he,hodd.neg_one_pow]

#print axioms logNumerator_real
#print axioms binomial
end Sigma2.EntropyPolynomial
