import Sigma2.UpperEntropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
open scoped BigOperators
open Filter
namespace Sigma2.UpperEntropySlack

/-- Entropy is continuous at zero as well as at positive probabilities. -/
theorem continuous_term : Continuous entropyTerm := by
  have heq : entropyTerm=(fun p : ℝ => -(p*Real.log p)/Real.log 2) := by
    funext p
    unfold entropyTerm
    ring
  rw [heq]
  exact Real.continuous_mul_log.neg.div_const (Real.log 2)

/-- Uniform rational slacks are exact on a compact feasible set. The feasible
point may vary with the precision; compactness supplies a single exact witness. -/
theorem compact_slack_iff {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    (K : Set X) (hK : IsCompact K) (f : X → ℝ) (hf : Continuous f)
    (A : ℕ → X → ℝ)
    (hA : ∀ k x,x∈K → |A k x-f x|≤1/(k+1:ℝ)) (B : ℝ) :
    (∃ x∈K,f x≤B) ↔ ∀ k,∃ x∈K,A k x≤B+1/(k+1:ℝ) := by
  constructor
  · rintro ⟨x,hx,hfB⟩ k
    refine ⟨x,hx,?_⟩
    have hh := (abs_le.mp (hA k x hx)).2
    linarith
  · intro h
    choose x hx hB using h
    obtain ⟨z,hz,φ,hφ,hlim⟩ := hK.tendsto_subseq hx
    refine ⟨z,hz,?_⟩
    have hden : Tendsto (fun n => (φ n:ℝ)+1) atTop atTop :=
      tendsto_atTop_mono (fun n => by change (φ n:ℝ)≤(φ n:ℝ)+1; linarith) (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
    have hzero := hden.const_div_atTop (1:ℝ)
    have hupper : Tendsto (fun n => B+2*(1/(φ n+1:ℝ))) atTop (nhds B) := by
      simpa using tendsto_const_nhds.add (hzero.const_mul 2)
    apply le_of_tendsto_of_tendsto (hf.continuousAt.tendsto.comp hlim) hupper
    apply Eventually.of_forall
    intro n
    have hh := (abs_le.mp (hA (φ n) (x (φ n)) (hx (φ n)))).1
    have hb := hB (φ n)
    change f (x (φ n))≤B+2*(1/(φ n+1:ℝ))
    linarith

/-- The finite entropy approximation intersection, once the non-entropy finite
matrix constraints have been packaged as a compact feasible set. -/
theorem entropy_compact_slack_iff {X : Type} [TopologicalSpace X] [FirstCountableTopology X]
    (K : Set X) (hK : IsCompact K) (n : ℕ) (p : X → Fin (n+1) → ℝ)
    (hp : ∀ i,Continuous (fun x => p x i))
    (hsimplex : ∀ x,x∈K → (∀ i,0≤p x i) ∧ (∑ i,p x i)=1)
    (H : ℕ → Polynomial ℚ)
    (hH : ∀ k (q : Fin (n+1) → ℝ),(∀ i,0≤q i) → (∑ i,q i)=1 →
      |(∑ i,(H k).eval₂ (algebraMap ℚ ℝ) (q i))-(∑ i,entropyTerm (q i))|≤1/(k+1:ℝ))
    (B : ℝ) :
    (∃ x∈K,(∑ i,entropyTerm (p x i))≤B) ↔
      ∀ k,∃ x∈K,(∑ i,(H k).eval₂ (algebraMap ℚ ℝ) (p x i))≤B+1/(k+1:ℝ) := by
  apply compact_slack_iff K hK _ _ _ _ B
  · exact continuous_finsetSum _ (fun i _ => continuous_term.comp (hp i))
  · intro k x hx
    exact hH k (p x) (hsimplex x hx).1 (hsimplex x hx).2

end Sigma2.UpperEntropySlack


