import Sigma2.UpperFiniteOperators

noncomputable section
open scoped BigOperators ComplexOrder
open Filter
namespace Sigma2.UpperFiniteAmplitudes
open UpperFiniteOperators

/-- Zero extension of a finite diagonal. -/
def pad (N : ℕ) (d : Fin N → ℝ) (i : ℕ) : ℝ :=
  if hi : i<N then d ⟨i,hi⟩ else 0

@[simp] theorem pad_fin (N : ℕ) (d : Fin N → ℝ) (i : Fin N) : pad N d i = d i := by
  simp [pad]

theorem pad_zero (N : ℕ) (d : Fin N → ℝ) (i : ℕ) (hi : N ≤ i) : pad N d i = 0 := by
  simp [pad,Nat.not_lt.mpr hi]

theorem pad_nonneg (N : ℕ) (d : Fin N → ℝ) (hd : ∀ i,0≤d i) :
    ∀ i,0≤pad N d i := by
  intro i
  unfold pad
  split_ifs
  · exact hd _
  · exact le_rfl

theorem pad_antitone (N : ℕ) (d : Fin N → ℝ) (hd : ∀ i,0≤d i) (ha : Antitone d) :
    Antitone (pad N d) := by
  intro i j hij
  unfold pad
  split_ifs with hj hi
  · exact ha hij
  · omega
  · exact hd _
  · exact le_rfl

theorem pad_hasSum (N : ℕ) (d : Fin N → ℝ) :
    HasSum (fun i => pad N d i ^ 2) (∑ i,d i^2) := by
  classical
  have h (i : ℕ) (hi : i ∉ Finset.range N) : pad N d i ^ 2 = 0 := by
    rw [pad_zero N d i (by simpa using hi),zero_pow (by decide : 2≠0)]
  have hh : HasSum (fun i => pad N d i ^ 2) (∑ i ∈ Finset.range N,pad N d i ^ 2) :=
    hasSum_sum_of_ne_finset_zero h
  convert hh using 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => pad N d i^2)]
  simp

theorem pad_diagonal (N : ℕ) (d : Fin N → ℝ) :
    UpperAmplitudes.Diagonal (extend N (Matrix.diagonal (fun i => (d i : ℂ)))) (pad N d) := by
  intro i j
  simp only [extend_entry,Matrix.diagonal_apply,pad]
  by_cases hi : i<N <;> by_cases hj : j<N <;> by_cases hij : i=j <;>
    simp [hi,hj,hij,Fin.ext_iff]

theorem pad_mem_family (n : ℕ) (d : Fin (n+1) → ℝ) (κ : ℝ)
    (h0 : d 0=1) (hd : ∀ i,0≤d i) (ha : Antitone d) (hb : (∑ i,d i^2)≤κ) :
    extend (n+1) (Matrix.diagonal (fun i => (d i : ℂ))) ∈ UpperAmplitudes.Family κ := by
  refine ⟨pad (n+1) d,pad_diagonal _ _,?_,pad_nonneg _ _ hd,pad_antitone _ _ hd ha,
    (pad_hasSum _ _).summable,(pad_hasSum _ _).tsum_eq.trans_le hb⟩
  simpa [pad] using h0

/-- Every sequence of feasible finite amplitudes admits an operator-norm convergent
subsequence retaining its first coordinate, order, and squared-sum budget. -/
theorem exists_norm_subsequence (κ : ℝ) (d : (n : ℕ) → Fin (n+1) → ℝ)
    (h0 : ∀ n,d n 0=1) (hd : ∀ n i,0≤d n i) (ha : ∀ n,Antitone (d n))
    (hb : ∀ n,(∑ i,d n i^2)≤κ) :
    ∃ (D : Op) (e : ℕ → ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧
      UpperAmplitudes.Diagonal D e ∧ e 0=1 ∧ (∀ i,0≤e i) ∧ Antitone e ∧
      Summable (fun i => e i^2) ∧ (∑' i,e i^2)≤κ ∧
      Tendsto (fun n => extend (φ n+1) (Matrix.diagonal (fun i => (d (φ n) i : ℂ))))
        atTop (nhds D) := by
  obtain ⟨D,⟨e,hdiag,he0,hepos,heanti,hesum,hebudget⟩,φ,hφ,hlim⟩ :=
    (UpperAmplitudes.compact_family κ).tendsto_subseq
      (fun n => pad_mem_family n (d n) κ (h0 n) (hd n) (ha n) (hb n))
  exact ⟨D,e,φ,hφ,hdiag,he0,hepos,heanti,hesum,hebudget,hlim⟩

/-- A sorted square-summable diagonal is compact in the fixed Hilbert model. -/
theorem diagonal_compact (D : Op) (e : ℕ → ℝ) (hdiag : UpperAmplitudes.Diagonal D e)
    (he : ∀ i,0≤e i) (ha : Antitone e) (hs : Summable (fun i => e i^2)) :
    IsCompactOperator D := by
  let T (N : ℕ) : Op := extend N (Matrix.diagonal (fun i => (e i : ℂ)))
  have htail : Tendsto e atTop (nhds 0) := by
    have hh := hs.tendsto_atTop_zero.sqrt
    simpa only [Real.sqrt_sq (he _),Real.sqrt_zero] using hh
  have hbound (N : ℕ) : ‖T N-D‖ ≤ e N := by
    apply UpperAmplitudes.norm_sub_le (pad_diagonal N (fun i => e i)) hdiag (e N) (he N)
    intro i
    by_cases hi : i<N
    · simp [pad,hi,he N]
    · rw [pad_zero N (fun i => e i) i (Nat.le_of_not_gt hi),zero_sub,abs_neg,
        abs_of_nonneg (he i)]
      exact ha (Nat.le_of_not_gt hi)
  have hlim : Tendsto T atTop (nhds D) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hbound htail
  apply isClosed_setOfPred_isCompactOperator.mem_of_tendsto hlim
  exact Eventually.of_forall fun n => extend_compact _ _

end Sigma2.UpperFiniteAmplitudes
