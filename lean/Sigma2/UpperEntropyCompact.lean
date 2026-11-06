import Sigma2.UpperEntropySlack

noncomputable section
open scoped BigOperators
open Filter
namespace Sigma2.UpperEntropyCompact

/-- The explicit logarithmic entropy tail denominator diverges effectively in dimension. -/
theorem tail_bound_tendsto_zero (B : ℝ) :
    Tendsto (fun n : ℕ => B/(Real.log (n+2:ℝ)/Real.log 2)) atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun n => by change (n:ℝ) ≤ (n:ℝ)+2; linarith)
      tendsto_natCast_atTop_atTop
  exact (Tendsto.atTop_div_const (Real.log_pos (by norm_num : (1:ℝ)<2))
    (Real.tendsto_log_atTop.comp hn)).const_div_atTop B

/-- Uniform entropy bounds prevent mass escaping to infinity in sorted spectra.
The limit keeps normalization and has a summable entropy series with the same bound. -/
theorem exists_probability_subsequence (p : ℕ → ℕ → ℝ) (B : ℝ)
    (hp : ∀ n i,0 ≤ p n i) (hs : ∀ n,Summable (p n))
    (ht : ∀ n,(∑' i,p n i)=1) (ha : ∀ n,Antitone (p n))
    (hH : ∀ n,Summable (fun i => entropyTerm (p n i)))
    (hB : ∀ n,(∑' i,entropyTerm (p n i)) ≤ B) :
    ∃ (q : ℕ → ℝ) (φ : ℕ → ℕ),StrictMono φ ∧
      (∀ i,0 ≤ q i) ∧ Summable q ∧ (∑' i,q i)=1 ∧ Antitone q ∧
      Summable (fun i => entropyTerm (q i)) ∧ (∑' i,entropyTerm (q i)) ≤ B ∧
      ∀ i,Tendsto (fun n => p (φ n) i) atTop (nhds (q i)) := by
  have hp1 n i : p n i ≤ 1 :=
    ((hs n).le_tsum i (fun j _ => hp n j)).trans_eq (ht n)
  obtain ⟨q,hq,φ,hφ,hlim⟩ :=
    (isCompact_univ_pi (fun _ : ℕ => isCompact_Icc : ∀ _ : ℕ,IsCompact (Set.Icc (0:ℝ) 1))).tendsto_subseq
      (fun n i _ => ⟨hp n i,hp1 n i⟩)
  have hc i : Tendsto (fun n => p (φ n) i) atTop (nhds (q i)) :=
    (continuous_apply i).tendsto _ |>.comp hlim
  have hq0 i : 0 ≤ q i := (hq i (Set.mem_univ i)).1
  have hq1 i : q i ≤ 1 := (hq i (Set.mem_univ i)).2
  have hqa : Antitone q := by
    intro i j hij
    exact le_of_tendsto_of_tendsto (hc j) (hc i)
      (Eventually.of_forall fun n => ha (φ n) hij)
  have hsum (s : Finset ℕ) : ∑ i ∈ s,q i ≤ 1 := by
    apply le_of_tendsto (tendsto_finsetSum s (fun i _ => hc i))
    exact Eventually.of_forall fun n =>
      ((hs (φ n)).sum_le_tsum s (fun i _ => hp (φ n) i)).trans_eq (ht (φ n))
  have hqs : Summable q := summable_of_sum_le hq0 hsum
  have hqsum : (∑' i,q i)=1 := by
    apply le_antisymm (hqs.tsum_le_of_sum_le hsum)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (tail_bound_tendsto_zero B) ε hε
    have hsmall : B/(Real.log (N+2:ℝ)/Real.log 2) < ε := by
      have hh := hN N le_rfl
      rw [Real.dist_eq,sub_zero] at hh
      exact (le_abs_self _).trans_lt hh
    have hpart : 1-B/(Real.log (N+2:ℝ)/Real.log 2) ≤ ∑ i ∈ Finset.range (N+1),q i := by
      apply le_of_tendsto_of_tendsto tendsto_const_nhds
        (tendsto_finsetSum _ (fun i _ => hc i))
      apply Eventually.of_forall
      intro n
      have htail := UpperEntropy.tail (p (φ n)) (hp (φ n)) (hs (φ n)) (ht (φ n))
        (ha (φ n)) (hH (φ n)) B (hB (φ n)) N
      have hsplit := (hs (φ n)).sum_add_tsum_nat_add (N+1)
      rw [ht (φ n)] at hsplit
      simp only [← Nat.add_assoc] at hsplit
      linarith
    have hle := hqs.sum_le_tsum (Finset.range (N+1)) (fun i _ => hq0 i)
    linarith
  have hqH0 i : 0 ≤ entropyTerm (q i) := EntropyDomination.entropy_nonneg (hq0 i) (hq1 i)
  have hsumH (s : Finset ℕ) : ∑ i ∈ s,entropyTerm (q i) ≤ B := by
    apply le_of_tendsto (tendsto_finsetSum s (fun i _ =>
      UpperEntropySlack.continuous_term.continuousAt.tendsto.comp (hc i)))
    exact Eventually.of_forall fun n =>
      ((hH (φ n)).sum_le_tsum s (fun i _ =>
        EntropyDomination.entropy_nonneg (hp (φ n) i) (hp1 (φ n) i))).trans (hB (φ n))
  have hqHs : Summable (fun i => entropyTerm (q i)) := summable_of_sum_le hqH0 hsumH
  exact ⟨q,φ,hφ,hq0,hqs,hqsum,hqa,hqHs,hqHs.tsum_le_of_sum_le hsumH,hc⟩

end Sigma2.UpperEntropyCompact
