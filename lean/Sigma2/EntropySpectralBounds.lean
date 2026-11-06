import Sigma2.EntropyMinMax

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.EntropyMinMax

lemma spectral_series_summable (p : ℕ → ℝ) (u : ℕ → H)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (hu : Orthonormal ℂ u) (v : H) :
    Summable (fun i => ((p i : ℂ) * inner ℂ (u i) v) • u i) := by
  apply (hs.mul_right ‖v‖).of_norm_bounded
  intro i
  calc
    _ = p i * ‖inner ℂ (u i) v‖ := by
      simp [norm_smul, hu.norm_eq_one, abs_of_nonneg (hp i)]
    _ ≤ p i * ‖v‖ := mul_le_mul_of_nonneg_left
      (by simpa only [hu.norm_eq_one, one_mul] using norm_inner_le_norm (u i) v) (hp i)

lemma spectral_term_real (p : ℝ) (u v : H) :
    (inner ℂ v (((p : ℂ) * inner ℂ u v) • u)).re = p * ‖inner ℂ u v‖^2 := by
  rw [inner_smul_right, mul_assoc, ← inner_conj_symm v u, Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- The quadratic form of a norm-convergent orthogonal spectral expansion. -/
theorem rayleigh_spectral (h : Density) (p : ℕ → ℝ) (u : ℕ → H)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (hu : Orthonormal ℂ u)
    (he : ∀ v, h.op v = ∑' i, ((p i : ℂ) * inner ℂ (u i) v) • u i) (v : H) :
    HasSum (fun i => p i * ‖inner ℂ (u i) v‖^2) (inner ℂ v (h.op v)).re := by
  have hh := ((spectral_series_summable p u hp hs hu v).hasSum.mapL
    (innerSL ℂ v)).mapL Complex.reCLM
  simpa only [innerSL_apply_apply, Complex.reCLM_apply, spectral_term_real, ← he] using hh

/-- Removing the first n spectral vectors bounds the remaining quadratic form.
Only the reference spectrum is used here; no simultaneous diagonalization occurs. -/
theorem spectral_tail_upper (h : Density) (p : ℕ → ℝ) (u : ℕ → H)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (hu : Orthonormal ℂ u)
    (he : ∀ v, h.op v = ∑' i, ((p i : ℂ) * inner ℂ (u i) v) • u i)
    (n : ℕ) (a : ℝ) (ha : 0 ≤ a) (htail : ∀ i, n ≤ i → p i ≤ a)
    (v : H) (hv : ∀ i : Fin n, inner ℂ (u i.val) v = 0) :
    (inner ℂ v (h.op v)).re ≤ a * ‖v‖^2 := by
  have hh := rayleigh_spectral h p u hp hs hu he v
  rw [← hh.tsum_eq]
  calc
    _ ≤ ∑' i, a * ‖inner ℂ (u i) v‖^2 := by
      apply hh.summable.tsum_le_tsum _ ((hu.inner_products_summable v).mul_left a)
      intro i
      by_cases hi : i < n
      · simp [hv ⟨i, hi⟩]
      · exact mul_le_mul_of_nonneg_right (htail i (by omega)) (sq_nonneg _)
    _ = a * (∑' i, ‖inner ℂ (u i) v‖^2) := tsum_mul_left
    _ ≤ a * ‖v‖^2 := mul_le_mul_of_nonneg_left (hu.tsum_inner_products_le v) ha

#print axioms spectral_series_summable
#print axioms spectral_term_real
#print axioms rayleigh_spectral
#print axioms spectral_tail_upper
end Sigma2.EntropyMinMax


