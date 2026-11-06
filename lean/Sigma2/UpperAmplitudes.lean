import Sigma2.UpperAnalytic

noncomputable section
open scoped BigOperators ComplexOrder ENNReal
open Filter
namespace Sigma2.UpperAmplitudes

def Diagonal (T : Op) (d : ℕ → ℝ) : Prop :=
  ∀ i j, entry T i j = if i=j then (d i : ℂ) else 0

theorem diagonal_apply {T : Op} {d : ℕ → ℝ} (hd : Diagonal T d) (v : H) (i : ℕ) :
    T v i=(d i:ℂ)*v i := by
  rw [TensorLifts.operator_coordinates]
  simp_rw [hd i]
  simp

theorem norm_sub_le {T U : Op} {d e : ℕ → ℝ} (hT : Diagonal T d) (hU : Diagonal U e)
    (C : ℝ) (hC : 0 ≤ C) (hde : ∀ i, |d i-e i| ≤ C) : ‖T-U‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  calc
    ‖(T-U) v‖ ≤ ‖(C:ℂ) • v‖ := by
      apply lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0)
      intro i
      simp only [ContinuousLinearMap.sub_apply,lp.coeFn_sub,Pi.sub_apply,
        diagonal_apply hT,diagonal_apply hU,← sub_mul,norm_mul,
        ← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
        lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hde i) (norm_nonneg _)
    _ = C*‖v‖ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]

def Family (κ : ℝ) : Set Op := {T | ∃ d : ℕ → ℝ,
  Diagonal T d ∧ d 0=1 ∧ (∀ i,0≤d i) ∧ Antitone d ∧
  Summable (fun i => d i^2) ∧ (∑' i,d i^2)≤κ}

theorem compact_family (κ : ℝ) : IsCompact (Family κ) := by
  apply IsSeqCompact.isCompact
  intro T hT
  choose d hdiag hfirst hnonneg hanti hsumm hbudget using hT
  change ∀ n i j, entry (T n) i j = if i=j then (d n i:ℂ) else 0 at hdiag
  have hdc (n i : ℕ) : d n i ∈ Set.Icc (0:ℝ) 1 :=
    ⟨hnonneg n i, (hanti n (Nat.zero_le i)).trans_eq (hfirst n)⟩
  obtain ⟨e,he,φ,hφ,hconv⟩ :=
    (isCompact_univ_pi (fun _ : ℕ => isCompact_Icc : ∀ _ : ℕ, IsCompact (Set.Icc (0:ℝ) 1))).tendsto_subseq
      (fun n i _ => hdc n i)
  have hcoord (i : ℕ) : Tendsto (fun n => d (φ n) i) atTop (nhds (e i)) :=
    (continuous_apply i).tendsto _ |>.comp hconv
  have hnonneg' (i : ℕ) : 0 ≤ e i := he i (Set.mem_univ i) |>.1
  have hfirst' : e 0=1 := tendsto_nhds_unique (hcoord 0)
    (by simpa only [hfirst] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (nhds 1)))
  have hanti' : Antitone e := by
    intro i j hij
    exact le_of_tendsto_of_tendsto (hcoord j) (hcoord i) (Eventually.of_forall fun n => hanti (φ n) hij)
  have hsum' (s : Finset ℕ) : ∑ i ∈ s,e i^2 ≤ κ := by
    apply le_of_tendsto (tendsto_finset_sum s (fun i _ => (hcoord i).pow 2))
    exact Eventually.of_forall fun n => ((hsumm (φ n)).sum_le_tsum s (fun i _ => sq_nonneg _)).trans (hbudget (φ n))
  have hsumm' : Summable (fun i => e i^2) := summable_of_sum_le (fun i => sq_nonneg _) hsum'
  have hbudget' : (∑' i,e i^2)≤κ := hsumm'.tsum_le_of_sum_le hsum'
  have hcauchy : CauchySeq (T ∘ φ) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := exists_nat_gt (κ/(ε/4)^2)
    have htail (m i : ℕ) (hi : N ≤ i) : d m i ≤ ε/4 := by
      have hb := UpperAnalytic.square_tail (d m) (hanti m) (hnonneg m) (hsumm m) κ (hbudget m) i
      have hden : (0:ℝ) < i+1 := by positivity
      have hNi : (N:ℝ) ≤ i := by exact_mod_cast hi
      have hcut : κ/(i+1) < (ε/4)^2 := by
        apply (div_lt_iff₀ hden).mpr
        have hmul := (div_lt_iff₀ (by positivity : (0:ℝ)<(ε/4)^2)).mp hN
        nlinarith [sq_pos_of_pos (by positivity : (0:ℝ)<ε/4)]
      exact hb.trans (Real.sqrt_le_iff.mpr ⟨by positivity,le_of_lt hcut⟩)
    have hev : ∀ᶠ m in atTop, ∀ i ∈ Finset.range N, |d (φ m) i-e i| < ε/4 := by
      rw [eventually_all_finset]
      intro i _
      obtain ⟨M,hM⟩ := Metric.tendsto_atTop.mp (hcoord i) (ε/4) (by positivity)
      exact eventually_atTop.mpr ⟨M,fun m hm => by simpa [Real.dist_eq] using hM m hm⟩
    obtain ⟨M,hM⟩ := eventually_atTop.mp hev
    refine ⟨M,?_⟩
    intro m hm l hl
    have hbound : ‖T (φ m)-T (φ l)‖ ≤ ε/2 := by
      apply norm_sub_le (hdiag (φ m)) (hdiag (φ l)) (ε/2) (by positivity)
      intro i
      by_cases hi : i<N
      · have ha := hM m hm i (Finset.mem_range.mpr hi)
        have hb := hM l hl i (Finset.mem_range.mpr hi)
        calc
          |d (φ m) i-d (φ l) i| ≤ |d (φ m) i-e i|+|d (φ l) i-e i| := by
            simpa only [abs_sub_comm (e i) (d (φ l) i)] using
              abs_sub_le (d (φ m) i) (e i) (d (φ l) i)
          _ ≤ ε/2 := by linarith
      · have ha := htail (φ m) i (Nat.le_of_not_gt hi)
        have hb := htail (φ l) i (Nat.le_of_not_gt hi)
        exact (abs_sub_le_iff.mpr ⟨by linarith [hnonneg (φ l) i],by linarith [hnonneg (φ m) i]⟩)
    exact lt_of_le_of_lt (by simpa [dist_eq_norm] using hbound) (by linarith)
  obtain ⟨U,hU⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hU' : Tendsto (T ∘ φ) atTop (nhds U) := hU
  have hdiag' : Diagonal U e := by
    intro i j
    have hij : Tendsto (fun n => entry (T (φ n)) i j) atTop (nhds (entry U i j)) := by
      exact ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i).continuous.tendsto _).comp
        (((show Continuous (fun L : Op => L (basis j)) from
          continuous_id.clm_apply continuous_const).tendsto U).comp hU')
    apply tendsto_nhds_unique hij
    simp only [hdiag]
    split_ifs
    · exact Complex.continuous_ofReal.continuousAt.tendsto.comp (hcoord i)
    · exact tendsto_const_nhds
  exact ⟨U,⟨e,hdiag',hfirst',hnonneg',hanti',hsumm',hbudget'⟩,φ,hφ,hU⟩

end Sigma2.UpperAmplitudes
