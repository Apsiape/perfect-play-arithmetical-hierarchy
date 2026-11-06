import Sigma2.EntropySpectrum
import Sigma2.EntropyTrace

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.EntropySpectrum

/-- Every density has an ordered spectral probability witness. The kernel may be
omitted when infinitely many positive eigenvalues are present; otherwise the
complete eigenbasis provides the required orthonormal zero-eigenvector tail. -/
theorem ordered_density_witness (h : Density) :
    ∃ (q : ℕ → ℝ) (u : ℕ → H),
      (∀ i, 0 ≤ q i) ∧ Summable q ∧ (∑' i, q i) = 1 ∧
      Orthonormal ℂ u ∧ Antitone q ∧
      (∀ v, h.op v = ∑' i, ((q i : ℂ) * inner ℂ (u i) v) • u i) := by
  obtain ⟨b, q, hq, he⟩ := exists_hilbert_eigenbasis h
  obtain ⟨hs, hsum⟩ := eigenbasis_probability h b q he
  obtain ⟨f, hord, hcover⟩ := EntropyEnumeration.exists_ordered_embedding q hq hs
  have hz (i : ℕ) (hi : i ∉ Set.range f) : q i = 0 := by
    by_contra hn
    exact hi (hcover i hn)
  have hprob : HasSum (fun i => q (f i)) 1 :=
    (f.injective.hasSum_iff hz).mpr (hs.hasSum_iff.mpr hsum)
  refine ⟨q ∘ f, b ∘ f, fun i => hq (f i), hprob.summable, hprob.tsum_eq,
    b.orthonormal.comp f f.injective, hord, ?_⟩
  intro v
  have hzero (i : ℕ) (hi : i ∉ Set.range f) :
      ((q i : ℂ) * inner ℂ (b i) v) • b i = 0 := by simp [hz i hi]
  have hh := (f.injective.hasSum_iff hzero).mpr
    (EntropyMinMax.spectral_series_summable q b hq hs b.orthonormal v).hasSum
  exact (hh.tsum_eq.trans (eigenbasis_expansion h b q he v).symm).symm

/-- Finite entropy passes to any positive operator dominated by a positive
multiple of the reference density, without a commutation hypothesis. -/
theorem finite_entropy_of_dominated (h g : Density) (r : ℝ) (hr : 0 < r)
    (hd : Positive (h.op - (r : ℂ) • g.op))
    (hh : FiniteDensityEntropy h) : FiniteDensityEntropy g := by
  obtain ⟨p, u, hp, hs, hsum, hu, he, hent, hord⟩ :=
    EntropyEnumeration.ordered_entropy_witness h hh
  obtain ⟨q, w, hq, hqs, hqsum, hw, hqord, hge⟩ := ordered_density_witness g
  exact EntropyMinMax.entropy_of_ordered_spectra h g r hr hd p q u w
    hp hs hsum hu he hord hent hq hqs hqsum hw hqord hge

#print axioms ordered_density_witness
#print axioms finite_entropy_of_dominated
end Sigma2.EntropySpectrum
