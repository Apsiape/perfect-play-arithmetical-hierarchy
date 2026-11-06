import Sigma2.EntropySpectralBounds

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.EntropyMinMax

/-- Evaluation on a spectral vector needs no completeness of the eigenfamily. -/
theorem apply_spectral_vector (h : Density) (p : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ v, h.op v = ∑' i, ((p i : ℂ) * inner ℂ (u i) v) • u i) (k : ℕ) :
    h.op (u k) = (p k : ℂ) • u k := by
  rw [he]
  simp [orthonormal_iff_ite.mp hu, mul_ite, ite_smul]

lemma finite_orthonormal_norm {m : ℕ} (w : Fin m → H) (hw : Orthonormal ℂ w)
    (c : Fin m → ℂ) : ‖∑ i, c i • w i‖^2 = ∑ i, ‖c i‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ]
  change (inner ℂ (∑ i, c i • w i) (∑ i, c i • w i)).re = _
  rw [hw.inner_sum c c Finset.univ]
  change Complex.reCLM (∑ i, (starRingEnd ℂ) (c i) * c i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change ((starRingEnd ℂ) (c i) * c i).re = ‖c i‖^2
  rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

lemma coefficient_real (z : ℂ) (q : ℝ) :
    (star z * (z * (q : ℂ))).re = q * ‖z‖^2 := by
  change ((starRingEnd ℂ) z * (z * (q : ℂ))).re = _
  rw [← mul_assoc, mul_comm ((starRingEnd ℂ) z) z, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- An entire finite spectral trial space has the expected Rayleigh lower bound. -/
theorem spectral_span_lower (g : Density) {m : ℕ} (q : Fin m → ℝ)
    (w : Fin m → H) (hw : Orthonormal ℂ w)
    (he : ∀ i, g.op (w i) = (q i : ℂ) • w i)
    (b : ℝ) (hb : ∀ i, b ≤ q i) (v : H)
    (hv : v ∈ Submodule.span ℂ (Set.range w)) :
    b * ‖v‖^2 ≤ (inner ℂ v (g.op v)).re := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  rw [finite_orthonormal_norm w hw c, Finset.mul_sum]
  have he' : g.op (∑ i, c i • w i) = ∑ i, (c i * (q i : ℂ)) • w i := by
    simp only [map_sum, map_smul, he, smul_smul]
  rw [he', hw.inner_sum c (fun i => c i * (q i : ℂ)) Finset.univ]
  change _ ≤ Complex.reCLM (∑ i, (starRingEnd ℂ) (c i) * (c i * (q i : ℂ)))
  rw [map_sum]
  apply Finset.sum_le_sum
  intro i _
  change b * ‖c i‖^2 ≤ (star (c i) * (c i * (q i : ℂ))).re
  rw [coefficient_real]
  exact mul_le_mul_of_nonneg_right (hb i) (sq_nonneg _)

/-- Weyl monotonicity for separately ordered spectral families, obtained from
finite trial spaces. It applies in infinite dimension and permits zero eigenvalues. -/
theorem ordered_eigenvalue_le (h g : Density) (r : ℝ) (hr : 0 < r)
    (hd : Positive (h.op - (r : ℂ) • g.op))
    (p q : ℕ → ℝ) (u w : ℕ → H)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (hu : Orthonormal ℂ u)
    (he : ∀ v, h.op v = ∑' i, ((p i : ℂ) * inner ℂ (u i) v) • u i)
    (hpord : Antitone p) (hqord : Antitone q) (hw : Orthonormal ℂ w)
    (hge : ∀ i, g.op (w i) = (q i : ℂ) • w i) (n : ℕ) :
    r * q n ≤ p n := by
  apply minmax_bound h g r (p n) (q n) hr hd n
    (fun i => u i.val) (fun i => w i.val)
    ((hw.comp _ Fin.val_injective).linearIndependent)
  · intro v hv
    exact spectral_tail_upper h p u hp hs hu he n (p n) (hp n)
      (fun i hi => hpord hi) v hv
  · intro v hv
    exact spectral_span_lower g (fun i : Fin (n+1) => q i.val)
      (fun i => w i.val) (hw.comp _ Fin.val_injective) (fun i => hge i.val)
      (q n) (fun i => hqord (by omega)) v hv

/-- The entropy bridge once the two ordered spectral witnesses are constructed.
This theorem proves the noncommuting comparison rather than postulating it. -/
theorem entropy_of_ordered_spectra (h g : Density) (r : ℝ) (hr : 0 < r)
    (hd : Positive (h.op - (r : ℂ) • g.op))
    (p q : ℕ → ℝ) (u w : ℕ → H)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (hpsum : (∑' i, p i) = 1)
    (hu : Orthonormal ℂ u)
    (he : ∀ v, h.op v = ∑' i, ((p i : ℂ) * inner ℂ (u i) v) • u i)
    (hpord : Antitone p) (hent : Summable (fun i => entropyTerm (p i)))
    (hq : ∀ i, 0 ≤ q i) (hqs : Summable q) (hqsum : (∑' i, q i) = 1)
    (hw : Orthonormal ℂ w) (hqord : Antitone q)
    (hge : ∀ v, g.op v = ∑' i, ((q i : ℂ) * inner ℂ (w i) v) • w i) :
    FiniteDensityEntropy g := by
  have hp1 (i : ℕ) : p i ≤ 1 := by
    rw [← hpsum]
    exact hs.le_tsum i (fun j _ => hp j)
  have hq1 (i : ℕ) : q i ≤ 1 := by
    rw [← hqsum]
    exact hqs.le_tsum i (fun j _ => hq j)
  refine ⟨q, w, hq, hqs, hqsum, hw, hge, ?_⟩
  apply EntropyDomination.summable_entropy_of_le p q (1/r) hp hp1 hq hq1
    (by positivity) _ hs hent
  intro i
  have hh := ordered_eigenvalue_le h g r hr hd p q u w hp hs hu he hpord hqord hw
    (apply_spectral_vector g q w hw hge) i
  have hdiv := (le_div_iff₀ hr).mpr (by nlinarith : q i * r ≤ p i)
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using hdiv

#print axioms apply_spectral_vector
#print axioms spectral_span_lower
#print axioms ordered_eigenvalue_le
#print axioms entropy_of_ordered_spectra
end Sigma2.EntropyMinMax


