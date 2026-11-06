import Sigma2.Preliminaries

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.FiniteStrategyApproximation

/-- The loss quadratic form is defined on every vector, before normalization. -/
def vectorLoss (G : Game) (M : Measurements G.scenario) (v : AB) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, (G.distribution x y : ℝ) *
    (if G.accepts x y a b then 0 else
      (inner ℂ v ((M.left x a * M.right y b) v)).re)

lemma vectorLoss_continuous (G : Game) (M : Measurements G.scenario) :
    Continuous (vectorLoss G M) := by
  unfold vectorLoss
  apply continuous_finsetSum
  intro x hx
  apply continuous_finsetSum
  intro y hy
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  by_cases h : G.accepts x y a b = true <;> simp [h]
  · fun_prop
  · fun_prop

lemma vectorLoss_pure (G : Game) (S : PureStrategy G.scenario) :
    vectorLoss G S.measurements S.vector = loss G (normalOfPure S) := by
  simp only [vectorLoss, loss, normalOfPure_probability, PureStrategy.probability]

/-- Finite coordinate vectors approximate any unit vector, with the same POVMs. -/
theorem pure_finite_approximation (G : Game) (S : PureStrategy G.scenario)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : PureStrategy G.scenario) (d : ℕ), 0 < d ∧ FiniteSupport T d ∧
      loss G (normalOfPure T) < loss G (normalOfPure S) + ε := by
  classical
  let u : Finset (ℕ × ℕ) → AB := fun F => ∑ ij ∈ F, lp.single 2 ij (S.vector ij)
  have hu : Filter.Tendsto u Filter.atTop (nhds S.vector) :=
    lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) S.vector
  let v : Finset (ℕ × ℕ) → AB := fun F => ((‖u F‖⁻¹ : ℝ) : ℂ) • u F
  have hv : Filter.Tendsto v Filter.atTop (nhds S.vector) := by
    have hn : Filter.Tendsto (fun F => ‖u F‖) Filter.atTop (nhds (1 : ℝ)) := by
      simpa only [S.unit] using hu.norm
    have hi := hn.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hi
    simpa only [v, Function.comp_def, inv_one, Complex.ofReal_one, one_smul] using hc.smul hu
  have hev : ∀ᶠ F in Filter.atTop,
      vectorLoss G S.measurements (v F) < loss G (normalOfPure S) + ε := by
    have ht := (vectorLoss_continuous G S.measurements).continuousAt.tendsto.comp hv
    apply (tendsto_order.mp ht).2
    rw [vectorLoss_pure]
    exact lt_add_of_pos_right _ hε
  have hne : ∀ᶠ F in Filter.atTop, u F ≠ 0 := by
    have hn : ∀ᶠ F in Filter.atTop, (0 : ℝ) < ‖u F‖ := by
      have ht := hu.norm
      apply (tendsto_order.mp ht).1
      rw [S.unit]
      norm_num
    exact hn.mono (fun F h => norm_pos_iff.mp h)
  obtain ⟨F, hF, hFne⟩ := (hev.and hne).exists
  have hvunit : ‖v F‖ = 1 := by
    simp only [v, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hFne)
  let T : PureStrategy G.scenario := ⟨S.measurements, v F, hvunit⟩
  let d := F.sup (fun ij => max ij.1 ij.2) + 1
  refine ⟨T, d, by dsimp [d]; omega, ?_, ?_⟩
  · intro i j hij
    have hnot : (i,j) ∉ F := by
      intro hmem
      have hb := Finset.le_sup (f := fun ij : ℕ × ℕ => max ij.1 ij.2) hmem
      dsimp [d] at hij
      rcases hij with hi | hj <;> omega
    change (((‖u F‖⁻¹ : ℝ) : ℂ) • u F) (i,j) = 0
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    suffices hz : u F (i,j) = 0 by rw [hz, mul_zero]
    dsimp only [u]
    simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]
    apply Finset.sum_eq_zero
    intro ij hij
    have hh : ij ≠ (i,j) := fun he => hnot (he ▸ hij)
    simp [Ne.symm hh]
  · simpa only [← vectorLoss_pure] using hF

/-- Normal correlations admit finite-vector pure approximants for any positive error. -/
theorem normal_finite_approximation (G : Game) (S : NormalStrategy G.scenario)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : PureStrategy G.scenario) (d : ℕ), 0 < d ∧ FiniteSupport T d ∧
      loss G (normalOfPure T) < loss G S + ε := by
  obtain ⟨U, hU⟩ := Preliminaries.purification S
  have hl : loss G (normalOfPure U) = loss G S := by
    simp only [loss, normalOfPure_probability]
    simp_rw [hU]
  simpa only [hl] using pure_finite_approximation G U ε hε

#print axioms pure_finite_approximation
#print axioms normal_finite_approximation
end Sigma2.FiniteStrategyApproximation
