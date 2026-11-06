import Sigma2.CompiledFockApproximation
import Sigma2.ValueOne

noncomputable section
open scoped BigOperators
namespace Sigma2.CompiledValue
open Sigma2.Value

/-- Section 7.1 / Eqs. (51)-(54): four separate diagonal-isometry defects,
one oriented zero-row event for each. Q,L,d depend only on the input game.
No clock-order factor or unspecified continuity modulus is present. -/
theorem four_defect_approximation {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ)
    (G : Game) (hG : decodeGame (CompiledReduction.gameCode f R hR e)=some G) :
    ∃ (Q : ℕ) (L d : Fin 4 → ℕ), 0<Q ∧ (∀ a, 0<L a ∧ 0<d a) ∧
      ∀ m, ∃ (S : PureStrategy G.scenario) (D : ℕ),
        0<D ∧ FiniteSupport S D ∧
        loss G (normalOfPure S) ≤ fourRowConstant Q L d * topMass m := by
  obtain ⟨C,hC,happrox⟩ := CompiledFockApproximation.finite_approximation hC R hR e G hG
  obtain ⟨N,hN⟩ := exists_nat_gt (363*C+1)
  have hNpos : 0<N := by
    by_contra hn
    have hz : N=0 := by omega
    rw [hz] at hN
    norm_num at hN
    linarith
  have hNreal : (1:ℝ)≤N := by exact_mod_cast hNpos
  have hcoef : C ≤ fourRowConstant 1 (fun _ => N) (fun _ => 1) := by
    norm_num [fourRowConstant]
    nlinarith [sq_nonneg ((N:ℝ)-1)]
  refine ⟨1,(fun _ => N),(fun _ => 1),by norm_num,(fun _ => ⟨hNpos,by norm_num⟩),?_⟩
  intro m
  obtain ⟨S,D,hD,hfin,hl⟩ := happrox m
  refine ⟨S,D,hD,hfin,hl.trans ?_⟩
  exact mul_le_mul_of_nonneg_right hcoef (by
    exact div_nonneg (by norm_num) (sub_nonneg.mpr
      (one_le_pow₀ (by norm_num : (1:ℝ)≤4))))

/-- Every output of the reduction satisfies the value-one promise, even NO outputs. -/
theorem value_one {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ)
    (G : Game) (hG : decodeGame (CompiledReduction.gameCode f R hR e)=some G) : ValueOne G := by
  obtain ⟨Q,L,d,_,_,happrox⟩ := four_defect_approximation hC R hR e G hG
  intro ε hε
  have ht : Filter.Tendsto (fun m => fourRowConstant Q L d * topMass m)
      Filter.atTop (nhds 0) := by
    simpa using top_mass_tendsto.const_mul (fourRowConstant Q L d)
  have hev : ∀ᶠ m in Filter.atTop, fourRowConstant Q L d * topMass m < ε :=
    (tendsto_order.mp ht).2 ε hε
  obtain ⟨m,hm⟩ := hev.exists
  obtain ⟨S,D,hD,hS,hl⟩ := happrox m
  exact ⟨S,D,hD,hS,hl.trans_lt hm⟩

theorem reduction_promised {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) :
    PromisedGame (CompiledReduction.gameCode f R hR e) := by
  obtain ⟨G,hG,_,_,_,_⟩ := CompiledReduction.gameCode_compiled hC R hR e
  refine ⟨G,hG,value_one hC R hR e G hG,?_⟩
  intro hfin
  exact (CompiledReduction.theorem_7_1_reduction hC R hR e).2.2 ⟨G,hG,hfin⟩


end Sigma2.CompiledValue
