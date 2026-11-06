import Sigma2.EntropyReindex

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.EntropyEnumeration

/-- A summable nonnegative sequence attains its maximum outside any finite set. -/
theorem exists_max_remaining (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (s : Finset ℕ) :
    ∃ k, k ∉ s ∧ ∀ j, j ∉ s → p j ≤ p k := by
  classical
  by_cases hpos : ∃ k, k ∉ s ∧ 0 < p k
  · obtain ⟨k, hk, hpk⟩ := hpos
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (hs.tendsto_atTop_zero.eventually (gt_mem_nhds hpk))
    let t := (Finset.range (max N (k+1))).filter (fun j => j ∉ s)
    have hkt : k ∈ t := by simp [t, hk]
    obtain ⟨a, ha, hmax⟩ := t.exists_max_image p ⟨k, hkt⟩
    refine ⟨a, (Finset.mem_filter.mp ha).2, fun j hj => ?_⟩
    by_cases hjN : j < max N (k+1)
    · exact hmax j (by simp [t, hj, hjN])
    · exact (hN j (by omega)).le.trans (hmax k hkt)
  · obtain ⟨k, hk⟩ := s.exists_notMem
    refine ⟨k, hk, fun j hj => ?_⟩
    have hj0 : p j = 0 := le_antisymm
      (not_lt.mp (fun h => hpos ⟨j, hj, h⟩)) (hp j)
    rw [hj0]
    exact hp k

noncomputable def pick (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (s : Finset ℕ) : ℕ :=
  Classical.choose (exists_max_remaining p hp hs s)

lemma pick_spec (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (s : Finset ℕ) :
    pick p hp hs s ∉ s ∧ ∀ j, j ∉ s → p j ≤ p (pick p hp hs s) :=
  Classical.choose_spec (exists_max_remaining p hp hs s)

noncomputable def used (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) : ℕ → Finset ℕ
  | 0 => ∅
  | n+1 => insert (pick p hp hs (used p hp hs n)) (used p hp hs n)

noncomputable def enumeration (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : Summable p) (n : ℕ) : ℕ := pick p hp hs (used p hp hs n)

lemma used_eq (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p) (n : ℕ) :
    used p hp hs n = (Finset.range n).image (enumeration p hp hs) := by
  classical
  induction n with
  | zero => rfl
  | succ n ih => simp [used, ih, Finset.range_add_one, enumeration]

theorem enumeration_injective (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    Function.Injective (enumeration p hp hs) := by
  classical
  suffices hh : ∀ a b, a < b → enumeration p hp hs a ≠ enumeration p hp hs b by
    intro a b hab
    rcases lt_trichotomy a b with h | h | h
    · exact False.elim (hh a b h hab)
    · exact h
    · exact False.elim (hh b a h hab.symm)
  intro a b hab heq
  have hn := (pick_spec p hp hs (used p hp hs b)).1
  apply hn
  have hm : enumeration p hp hs a ∈ used p hp hs b := by
    rw [used_eq]
    exact Finset.mem_image.mpr ⟨a, Finset.mem_range.mpr hab, rfl⟩
  change enumeration p hp hs b ∈ used p hp hs b
  rw [← heq]
  exact hm

theorem enumeration_antitone (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    Antitone (fun n => p (enumeration p hp hs n)) := by
  classical
  apply antitone_nat_of_succ_le
  intro n
  apply (pick_spec p hp hs (used p hp hs n)).2
  have hn := (pick_spec p hp hs (used p hp hs (n+1))).1
  exact fun h => hn (Finset.mem_insert_of_mem h)

theorem enumeration_covers (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    ∀ k, p k ≠ 0 → k ∈ Set.range (enumeration p hp hs) := by
  classical
  intro k hk
  by_contra hn
  have hpk : 0 < p k := lt_of_le_of_ne (hp k) (Ne.symm hk)
  have hsub := hs.comp_injective (enumeration_injective p hp hs)
  have hsmall := hsub.tendsto_atTop_zero.eventually (gt_mem_nhds hpk)
  obtain ⟨n, hsmall⟩ := hsmall.exists
  have hnot : k ∉ used p hp hs n := by
    rw [used_eq]
    intro hm
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hm
    exact hn ⟨a, ha⟩
  exact (not_lt_of_ge ((pick_spec p hp hs (used p hp hs n)).2 k hnot)) hsmall

/-- Greedy decreasing enumeration covers every positive entry, and supplies distinct
zero entries after the positive spectrum is exhausted. No faithfulness is assumed. -/
theorem exists_ordered_embedding (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p) :
    ∃ f : ℕ ↪ ℕ, Antitone (fun n => p (f n)) ∧
      ∀ k, p k ≠ 0 → k ∈ Set.range f := by
  exact ⟨⟨enumeration p hp hs, enumeration_injective p hp hs⟩,
    enumeration_antitone p hp hs, enumeration_covers p hp hs⟩

/-- Every finite-entropy spectral witness admits a decreasing reindexing,
with unchanged probability sum, operator expansion, and entropy summability. -/
theorem ordered_entropy_witness (h : Density) (hh : FiniteDensityEntropy h) :
    ∃ (p : ℕ → ℝ) (u : ℕ → H),
      (∀ i, 0 ≤ p i) ∧ Summable p ∧ (∑' i, p i) = 1 ∧
      Orthonormal ℂ u ∧
      (∀ v, h.op v = ∑' i, ((p i : ℂ) * inner ℂ (u i) v) • u i) ∧
      Summable (fun i => entropyTerm (p i)) ∧ Antitone p := by
  obtain ⟨p, u, hp, hs, hsum, hu, he, hent⟩ := hh
  obtain ⟨f, hord, hcover⟩ := exists_ordered_embedding p hp hs
  obtain ⟨hp', hs', hsum', hu', he', hent'⟩ :=
    EntropyMinMax.reindex_spectral_data h p u hp hs hsum hu he hent f hcover
  exact ⟨p ∘ f, u ∘ f, hp', hs', hsum', hu', he', hent', hord⟩

#print axioms exists_ordered_embedding
#print axioms ordered_entropy_witness
end Sigma2.EntropyEnumeration
