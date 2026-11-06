import Sigma2.EntropyOrdered

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.EntropyMinMax

/-- An injective enumeration may omit zero eigenspaces. It preserves the actual
spectral operator, probability sum and entropy, even when the kernel is nonzero.
For a finite positive spectrum the enumeration must still provide zero padding. -/
theorem reindex_spectral_data (h : Density) (p : ℕ → ℝ) (u : ℕ → H)
    (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (hpsum : (∑' i, p i)=1)
    (hu : Orthonormal ℂ u)
    (he : ∀ v, h.op v=∑' i, ((p i : ℂ)*inner ℂ (u i) v) • u i)
    (hent : Summable (fun i => entropyTerm (p i))) (f : ℕ ↪ ℕ)
    (hcover : ∀ i, p i≠0 → i ∈ Set.range f) :
    (∀ i, 0 ≤ p (f i)) ∧ Summable (fun i => p (f i)) ∧
    (∑' i, p (f i))=1 ∧ Orthonormal ℂ (fun i => u (f i)) ∧
    (∀ v, h.op v=∑' i, ((p (f i) : ℂ)*inner ℂ (u (f i)) v) • u (f i)) ∧
    Summable (fun i => entropyTerm (p (f i))) := by
  have hz (i : ℕ) (hi : i ∉ Set.range f) : p i=0 := by
    by_contra hn
    exact hi (hcover i hn)
  have hsum : HasSum (fun i => p (f i)) 1 :=
    (f.injective.hasSum_iff hz).mpr (hs.hasSum_iff.mpr hpsum)
  refine ⟨fun i => hp (f i), hsum.summable, hsum.tsum_eq,
    hu.comp f f.injective, ?_, ?_⟩
  · intro v
    have hzero (i : ℕ) (hi : i ∉ Set.range f) :
        ((p i : ℂ)*inner ℂ (u i) v) • u i=0 := by simp [hz i hi]
    have hh := (f.injective.hasSum_iff hzero).mpr
      ((spectral_series_summable p u hp hs hu v).hasSum)
    exact (hh.tsum_eq.trans (he v).symm).symm
  · have hzero (i : ℕ) (hi : i ∉ Set.range f) : entropyTerm (p i)=0 := by
      simp [hz i hi, entropyTerm]
    exact ((f.injective.hasSum_iff hzero).mpr hent.hasSum).summable

#print axioms reindex_spectral_data
end Sigma2.EntropyMinMax
