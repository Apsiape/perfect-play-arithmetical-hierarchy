import Sigma2.UpperEntropyFinite
import Sigma2.UpperEntropySlack
import Mathlib.Analysis.Matrix.Order

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix.Norms.Elementwise ENNReal
namespace Sigma2.UpperEntropyFeasible
open UpperFiniteOperators UpperFiniteBorn UpperEntropyFinite

local instance (m : ℕ) : FirstCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (FirstCountableTopology (Fin m → Fin m → ℂ))

/-- The finite loss is a continuous polynomial in the amplitudes and matrix entries. -/
theorem continuous_loss (G : Game) (m : ℕ) : Continuous (finiteLoss G m) := by
  unfold finiteLoss
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  apply continuous_finsetSum
  intro a _
  apply continuous_finsetSum
  intro b _
  split_ifs <;> fun_prop

/-- All finite constraints other than entropy form a closed set. -/
theorem closed_feasible (G : Game) (m : ℕ) (η : ℝ) :
    IsClosed {z : Data G.scenario m | Feasible G m η z} := by
  simp only [Feasible,Set.ofPred_and,Set.ofPred_forall]
  refine (isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)).inter
    ((isClosed_eq (by fun_prop) continuous_const).inter (?_ : IsClosed _))
  refine (?_ : IsClosed {z : Data G.scenario m | Antitone z.1}).inter ?_
  · change IsClosed {z : Data G.scenario m | ∀ i j : Fin m,i ≤ j → z.1 j ≤ z.1 i}
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_le (by fun_prop) (by fun_prop)
  · refine (isClosed_iInter fun i =>
      (isClosed_le continuous_const (by fun_prop)).inter
        (isClosed_eq (by fun_prop) (by fun_prop))).inter ?_
    refine (isClosed_iInter fun x => isClosed_iInter fun a =>
      Matrix.posSemidef_is_closed.preimage (by fun_prop)).inter ?_
    refine (isClosed_iInter fun y => isClosed_iInter fun b =>
      Matrix.posSemidef_is_closed.preimage (by fun_prop)).inter ?_
    refine (isClosed_iInter fun x => isClosed_eq (by fun_prop) continuous_const).inter ?_
    exact (isClosed_iInter fun y => isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_le (continuous_loss G m) continuous_const)

theorem entry_norm (T : Op) (i j : ℕ) : ‖entry T i j‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖T (basis j)‖ := lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) _ _
    _ ≤ ‖T‖*‖basis j‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖T‖ := by simp [basis,lp.norm_single]

theorem effect_entry_bound {a : ℕ} (m : ℕ)
    (E : Fin (a+1) → Matrix (Fin m) (Fin m) ℂ)
    (hp : ∀ a,(E a).PosSemidef) (hs : ∑ a,E a=1) (a : Fin (a+1)) (i j : Fin m) :
    ‖E a i j‖ ≤ 1 := by
  have he := congrArg (fun A : Matrix (Fin m) (Fin m) ℂ => A i j)
    (compress_effect m 0 a (E a))
  change entry (effect m 0 a (E a)) i j=E a i j at he
  rw [← he]
  exact (entry_norm _ i j).trans (effect_norm_le_one m 0 a E hp hs)

/-- Normalization and positivity bound every scalar and matrix coordinate by one. -/
theorem feasible_norm_le (G : Game) (m : ℕ) (η : ℝ) (z : Data G.scenario m)
    (hz : Feasible G m η z) : ‖z‖ ≤ 1 := by
  obtain ⟨hp,hs,ha,ht,hE,hF,hEs,hFs,hl⟩ := hz
  have hp1 i : z.1 i ≤ 1 := by
    exact (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)).trans_eq hs
  have ht1 i : z.2.1 i ≤ 1 := by nlinarith [(ht i).2,hp1 i]
  simp only [Prod.norm_def,max_le_iff,pi_norm_le_iff_of_nonneg zero_le_one,Matrix.norm_le_iff zero_le_one]
  refine ⟨(fun i => ?_),(fun i => ?_),?_,?_⟩
  · simpa only [Real.norm_eq_abs,abs_of_nonneg (hp i)] using hp1 i
  · simpa only [Real.norm_eq_abs,abs_of_nonneg (ht i).1] using ht1 i
  · intro x a i j
    exact effect_entry_bound m _ (hE x) (hEs x) a i j
  · intro y b i j
    exact effect_entry_bound m _ (hF y) (hFs y) b i j

/-- Compactness is proved for the exact finite feasible set, before entropy is imposed. -/
theorem compact_feasible (G : Game) (m : ℕ) (η : ℝ) :
    IsCompact {z : Data G.scenario m | Feasible G m η z} := by
  apply (isCompact_closedBall (0 : Data G.scenario m) 1).of_isClosed_subset
    (closed_feasible G m η)
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  exact feasible_norm_le G m η z hz

/-- Polynomial entropy slacks are exact on the finite POVM feasible set. -/
theorem slack_iff (G : Game) (n : ℕ) (η B : ℝ) (H : ℕ → Polynomial ℚ)
    (hH : ∀ k (p : Fin (n+1) → ℝ),(∀ i,0 ≤ p i) → (∑ i,p i)=1 →
      |(∑ i,(H k).eval₂ (algebraMap ℚ ℝ) (p i))-(∑ i,entropyTerm (p i))| ≤
        1/(k+1:ℝ)) :
    (∃ z : Data G.scenario (n+1),Feasible G (n+1) η z ∧
      (∑ i,entropyTerm (z.1 i)) ≤ B) ↔
    ∀ k,∃ z : Data G.scenario (n+1),Feasible G (n+1) η z ∧
      (∑ i,(H k).eval₂ (algebraMap ℚ ℝ) (z.1 i)) ≤ B+1/(k+1:ℝ) := by
  exact UpperEntropySlack.entropy_compact_slack_iff _ (compact_feasible G (n+1) η)
    n (fun z => z.1) (fun i => by fun_prop)
    (fun z hz => ⟨hz.1,hz.2.1⟩) H hH B

end Sigma2.UpperEntropyFeasible


