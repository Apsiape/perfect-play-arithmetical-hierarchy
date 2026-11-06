import Sigma2.UpperEntropySchedule
import Sigma2.UpperEntropyCanonical
import Sigma2.UpperEntropyOperatorLimits
import Sigma2.UpperWOTCompact
import Sigma2.UpperTransposeLimits

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open Filter
namespace Sigma2.UpperEntropyAssembly
open UpperFiniteAmplitudes UpperFiniteBorn UpperEntropyFinite UpperEntropySchedule

/-- An arbitrary finite witness can be put in canonical Schmidt coordinates. -/
theorem canonical_of_data (G : Game) (m : ℕ) (η : ℝ) (z : Data G.scenario m)
    (hf : Feasible G m η z) :
    ∃ S : PureStrategy G.scenario,
      S.vector=UpperSchmidtState.vector (pad m z.1) (pad_nonneg _ _ hf.1) (pad_summable _ _) ∧
      loss G (normalOfPure S) ≤ η := by
  obtain ⟨S,_,hl,h,hm,he⟩ := UpperEntropyCanonical.strategy_of_feasible G m η z hf
  have he' : ∀ v,(UpperSchmidtSpectrum.density S.vector S.unit).op v=
      ∑' i,((pad m z.1 i:ℂ)*inner ℂ (basis i) v) • basis i := by
    rw [← marginal_op_eq S h hm]
    exact he
  obtain ⟨T,hTv,hprob⟩ := UpperSchmidtState.exists_strategy S (pad m z.1) basis
    (pad_nonneg _ _ hf.1) (pad_summable _ _) ((pad_sum _ _).trans hf.2.1)
    basis_orthonormal he'
  refine ⟨T,hTv,?_⟩
  simpa only [loss,normalOfPure_probability,hprob] using hl

theorem povm_norm {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → Op)
    (hp : ∀ a,Positive (A a)) (hs : ∑ a,A a=1) (a : ι) : ‖A a‖ ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (hp a))).mpr
  apply sub_nonneg.mp
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  rw [← hs]
  exact Preliminaries.positive_sum_erase A hp a

/-- Entropy-tight canonical approximations assemble into a genuine perfect strategy.
The probability subsequence is refined once for both POVMs. -/
theorem perfect_of_sequence (G : Game) (p : ℕ → ℕ → ℝ) (B : ℝ)
    (hp : ∀ n i,0 ≤ p n i) (hs : ∀ n,Summable (p n))
    (ht : ∀ n,(∑' i,p n i)=1) (ha : ∀ n,Antitone (p n))
    (hH : ∀ n,Summable (fun i => entropyTerm (p n i)))
    (hB : ∀ n,(∑' i,entropyTerm (p n i)) ≤ B)
    (S : ℕ → PureStrategy G.scenario)
    (hv : ∀ n,(S n).vector=UpperSchmidtState.vector (p n) (hp n) (hs n))
    (hl : ∀ n,loss G (normalOfPure (S n)) ≤ 1/(n+1:ℝ)) :
    HasFiniteEntropyPerfect G := by
  obtain ⟨q,φ,hφ,hq,hqs,hqt,hqa,hqH,_,hlim⟩ :=
    UpperEntropyCompact.exists_probability_subsequence p B hp hs ht ha hH hB
  have hp1 n i : p n i ≤ 1 := ((hs n).le_tsum i (fun j _ => hp n j)).trans_eq (ht n)
  have hq1 i : q i ≤ 1 := (hqs.le_tsum i (fun j _ => hq j)).trans_eq hqt
  have hdp n i : |Real.sqrt (p n i)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (hp1 n i)
  have hde i : |Real.sqrt (q i)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.mpr (hq1 i)
  let D n := UpperSchmidtOperators.diagonalOp (fun i => Real.sqrt (p n i)) (hdp n)
  let D₀ := UpperSchmidtOperators.diagonalOp (fun i => Real.sqrt (q i)) hde
  have hdiag n : UpperAmplitudes.Diagonal (D n) (fun i => Real.sqrt (p n i)) :=
    UpperSchmidtOperators.diagonalOp_diagonal _ _
  have hdiag₀ : UpperAmplitudes.Diagonal D₀ (fun i => Real.sqrt (q i)) :=
    UpperSchmidtOperators.diagonalOp_diagonal _ _
  have hanti n : Antitone (fun i => Real.sqrt (p n i)) := fun i j hij => Real.sqrt_le_sqrt (ha n hij)
  have hanti₀ : Antitone (fun i => Real.sqrt (q i)) := fun i j hij => Real.sqrt_le_sqrt (hqa hij)
  have hss n : Summable (fun i => Real.sqrt (p n i)^2) := UpperSchmidtState.sqrt_summable _ (hp n) (hs n)
  have hss₀ := UpperSchmidtState.sqrt_summable q hq hqs
  have hbudget n : (∑' i,Real.sqrt (p n i)^2) ≤ 1 := by
    simpa only [Real.sq_sqrt (hp n _),ht n] using (le_refl (1:ℝ))
  have hbudget₀ : (∑' i,Real.sqrt (q i)^2) ≤ 1 := by
    simpa only [Real.sq_sqrt (hq _),hqt] using (le_refl (1:ℝ))
  have hD : Tendsto (fun n => D (φ n)) atTop (nhds D₀) :=
    UpperEntropyOperatorLimits.diagonal_norm_tendsto _ _ _ _
      (fun n => hdiag (φ n)) hdiag₀
      (fun n i => Real.sqrt_nonneg _) (fun n => hanti (φ n))
      (fun n => hss (φ n)) (fun n => hbudget (φ n))
      (fun i => Real.sqrt_nonneg _) hanti₀ hss₀ hbudget₀ (fun i => (hlim i).sqrt)
  let T (n : ℕ) : (QA G.scenario × AA G.scenario) ⊕ (QB G.scenario × BB G.scenario) → Op
    | .inl (x,a) => (S (φ n)).measurements.alice x a
    | .inr (y,b) => (S (φ n)).measurements.bob y b
  have hnorm n z : ‖T n z‖ ≤ 1 := by
    cases z with
    | inl z =>
        exact povm_norm _ ((S (φ n)).measurements.alice_pos z.1)
          ((S (φ n)).measurements.alice_sum z.1) z.2
    | inr z =>
        exact povm_norm _ ((S (φ n)).measurements.bob_pos z.1)
          ((S (φ n)).measurements.bob_sum z.1) z.2
  obtain ⟨L,ψ,hψ,_,hL⟩ := UpperWOTCompact.exists_common_subsequence T hnorm
  let A (x : QA G.scenario) (a : AA G.scenario) := L (.inl (x,a))
  let F (y : QB G.scenario) (b : BB G.scenario) := L (.inr (y,b))
  have hApos x a : Positive (A x a) := UpperWeakLimits.positive _ _ (hL (.inl (x,a)))
    (fun n => (S (φ (ψ n))).measurements.alice_pos x a)
  have hFpos y b : Positive (F y b) := UpperWeakLimits.positive _ _ (hL (.inr (y,b)))
    (fun n => (S (φ (ψ n))).measurements.bob_pos y b)
  have hAsum x : ∑ a,A x a=1 := UpperWeakLimits.sum_eq_one _ _ (fun a => hL (.inl (x,a)))
    (fun n => (S (φ (ψ n))).measurements.alice_sum x)
  have hFsum y : ∑ b,F y b=1 := UpperWeakLimits.sum_eq_one _ _ (fun b => hL (.inr (y,b)))
    (fun n => (S (φ (ψ n))).measurements.bob_sum y)
  let M := TensorLifts.measurements G.scenario A F hApos hFpos hAsum hFsum
  let Ftr n y b := UpperTranspose.transpose ((S n).measurements.bob y b)
  have htranspose n y b i j : entry (Ftr n y b) i j=entry ((S n).measurements.bob y b) j i :=
    UpperTranspose.transpose_entry _ i j
  have hvector n i j : (S n).vector (i,j)=entry (D n) i j := by
    rw [hv,UpperSchmidtState.vector_apply,hdiag]
  have hcompact := UpperFiniteAmplitudes.diagonal_compact D₀ _ hdiag₀
    (fun i => Real.sqrt_nonneg _) hanti₀ hss₀
  have hzero x y a b (hw : 0 < G.distribution x y) (hac : G.accepts x y a b=false) :
      M.alice x a*D₀*UpperTranspose.transpose (M.bob y b)=0 := by
    have hE : UpperWeakLimits.Converges
        (fun n => (S (φ (ψ n))).measurements.alice x a) (M.alice x a) := hL (.inl (x,a))
    have hF : UpperWeakLimits.Converges
        (fun n => Ftr (φ (ψ n)) y b) (UpperTranspose.transpose (M.bob y b)) :=
      UpperTransposeLimits.converges _ _ (hL (.inr (y,b)))
    have hconv := UpperCompact.sandwiches (fun n => D (φ (ψ n)))
      (fun n => (S (φ (ψ n))).measurements.alice x a)
      (fun n => Ftr (φ (ψ n)) y b) D₀ (M.alice x a) (UpperTranspose.transpose (M.bob y b))
      (hD.comp hψ.tendsto_atTop) hcompact hE hF
      ⟨1,fun n => povm_norm _ ((S (φ (ψ n))).measurements.alice_pos x)
        ((S (φ (ψ n))).measurements.alice_sum x) a⟩
      ⟨1,fun n => (UpperTranspose.transpose_norm_le _).trans
        (povm_norm _ ((S (φ (ψ n))).measurements.bob_pos y)
          ((S (φ (ψ n))).measurements.bob_sum y) b)⟩
    exact UpperEntropyLoss.zero_of_loss G S D Ftr htranspose hvector hl
      (φ ∘ ψ) (hφ.comp hψ) x y a b hw hac _ hconv
  let R : PureStrategy G.scenario :=
    ⟨M,UpperSchmidtState.vector q hq hqs,UpperSchmidtState.vector_unit q hq hqs hqt⟩
  refine ⟨normalOfPure R,UpperDiagonalVectors.perfect_of_losing_zero G R ?_,
    UpperEntropyCanonical.finite_marginal_entropy M q hq hqs hqt hqH⟩
  intro x y a b hw hac
  apply (UpperAnalytic.zero_sandwich M x y a b D₀ (UpperTranspose.transpose (M.bob y b))
    (UpperTranspose.transpose_entry _) R.vector ?_).mpr (hzero x y a b hw hac)
  intro i j
  change UpperSchmidtState.vector q hq hqs (i,j)=_
  rw [UpperSchmidtState.vector_apply,hdiag₀]

/-- Scheduled witnesses have a common entropy bound B+1 and hence a perfect limit. -/
theorem perfect_of_scheduled (G : Game) (B : ℕ) (h : ScheduledData G B) :
    HasFiniteEntropyPerfect G := by
  choose z hf he using h
  let p n := pad (stageIndex B n+1) (z n).1
  have hp n : ∀ i,0 ≤ p n i := pad_nonneg _ _ (hf n).1
  have hs n : Summable (p n) := pad_summable _ _
  have ht n : (∑' i,p n i)=1 := (pad_sum _ _).trans (hf n).2.1
  have ha n : Antitone (p n) := pad_antitone _ _ (hf n).1 (hf n).2.2.1
  have hH n : Summable (fun i => entropyTerm (p n i)) := summable_fin (stageIndex B n+1) _
    (fun i hi => by simp [p,pad_zero _ _ i hi,entropyTerm])
  have hbudget n : (∑' i,entropyTerm (p n i)) ≤ (B:ℝ)+1 := by
    rw [tsum_fin (stageIndex B n+1) _ (fun i hi => by simp [p,pad_zero _ _ i hi,entropyTerm])]
    have hslack : (1:ℝ)/(stageIndex B n+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hh := Nat.cast_nonneg (α := ℝ) (stageIndex B n)
      linarith
    calc
      _ ≤ (B:ℝ)+1/(stageIndex B n+1:ℝ) := by simpa only [p,pad_fin] using he n
      _ ≤ (B:ℝ)+1 := by linarith only [hslack]
  have hex n := canonical_of_data G (stageIndex B n+1) (1/(n+1:ℝ)) (z n) (hf n)
  choose S hv hl using hex
  exact perfect_of_sequence G p ((B:ℝ)+1) hp hs ht ha hH hbudget S hv hl

/-- The integer-budget scheduled feasibility characterization. -/
theorem scheduled_iff (G : Game) : HasFiniteEntropyPerfect G ↔ ∃ B,ScheduledData G B :=
  ⟨scheduled_of_perfect G,fun ⟨B,hB⟩ => perfect_of_scheduled G B hB⟩

end Sigma2.UpperEntropyAssembly
