import Sigma2.FockTruncationResiduals
import Sigma2.FiniteStrategyApproximation
import Sigma2.CompiledReduction

noncomputable section
open scoped BigOperators
namespace Sigma2.CompiledFockApproximation
open Sigma2.Tree Sigma2.Reduction Sigma2.FockTruncation Sigma2.ReductionFockModel

/-- Four diagonal residuals, with a depth-independent compiler constant. -/
theorem normal_approximation {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ)
    (G : Game) (hG : decodeGame (CompiledReduction.gameCode f R hR e)=some G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ∃ S : NormalStrategy G.scenario,
      loss G S ≤ (4*C)*(3/((4:ℝ)^(m+1)-1)) := by
  let M := decodeAutomaton (programCode R hR e)
  obtain ⟨C,hC,hcompile⟩ := CompilerSpecification.approximate_compilation hC (inputPresentation R hR e)
    (application_admissible M)
  refine ⟨C,hC,?_⟩
  intro m
  obtain ⟨q,hmq,hq⟩ := Nat.exists_infinite_primes (2^m)
  letI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨ζ,hprim,hsep⟩ := PrimePhase.good_root q hq
  have hnorm : ‖ζ‖=1 := (hprim.isOfFinOrder (NeZero.ne q)).norm_eq_one
  have hprog : ProgramCorrect R e M :=
    (Classical.choose_spec (effective_program R hR)).2 e
  have hsafe : ∀ t x,t ≤ q → run M (classicalPulse q) t x ≠ 2 := by
    intro t x ht
    exact hprog.2.1 q hq.pos t ht x
  have hz := symbol_no_halt_cut q M m hmq hsafe
  obtain ⟨S,hS⟩ := hcompile G hG (structural q m M ζ hnorm hsep)
  refine ⟨S,?_⟩
  change loss G S ≤ C * ((Compiler.applicationResiduals (applicationPresentation M)
    (structural q m M ζ hnorm hsep)).map (fun r => (trace ((FockTruncation.density q m).op*(star r*r))).re)).sum at hS
  rw [residual_sum q M ζ hnorm hsep m hprim hz] at hS
  nlinarith only [hS]

/-- Finite-vector strategies preserve the geometric rate, with fixed slack. -/
theorem finite_approximation {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ)
    (G : Game) (hG : decodeGame (CompiledReduction.gameCode f R hR e)=some G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m, ∃ (S : PureStrategy G.scenario) (D : ℕ),
      0<D ∧ FiniteSupport S D ∧ loss G (normalOfPure S) ≤ C*(3/((4:ℝ)^(m+1)-1)) := by
  obtain ⟨C,hC,happrox⟩ := normal_approximation hC R hR e G hG
  refine ⟨4*C+1,by positivity,?_⟩
  intro m
  obtain ⟨T,hT⟩ := happrox m
  have hp : 0 < 3/((4:ℝ)^(m+1)-1) :=
    div_pos (by norm_num) (sub_pos.mpr (one_lt_pow₀ (by norm_num) (by omega)))
  obtain ⟨S,D,hD,hfin,hl⟩ := FiniteStrategyApproximation.normal_finite_approximation G T _ hp
  refine ⟨S,D,hD,hfin,?_⟩
  nlinarith only [hl,hT]

#print axioms normal_approximation
#print axioms finite_approximation
end Sigma2.CompiledFockApproximation
