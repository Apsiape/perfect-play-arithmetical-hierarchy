import Sigma2.CompiledValue
import Sigma2.Upper
import Sigma2.CompilerContract

noncomputable section
namespace Sigma2

/-- Arithmetical many-one hardness, with no named own-result hypotheses. -/
theorem spatial_hard_of_compiler {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) : SigmaTwoHard SpatialPerfect := by
  intro S hS
  obtain ⟨R,hR,h⟩ := hS
  exact ⟨CompiledReduction.gameCode f R hR,CompiledReduction.gameCode_computable hC R hR,
    fun e => (h e).trans (CompiledReduction.theorem_7_1_reduction hC R hR e).1.symm⟩

theorem entropy_hard_of_compiler {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) : SigmaTwoHard EntropyPerfect := by
  intro S hS
  obtain ⟨R,hR,h⟩ := hS
  exact ⟨CompiledReduction.gameCode f R hR,CompiledReduction.gameCode_computable hC R hR,
    fun e => (h e).trans (CompiledReduction.theorem_7_1_reduction hC R hR e).2.1.symm⟩

theorem spatial_promise_hard_of_compiler {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) : PromiseHard SpatialPerfect PromisedGame := by
  intro S hS
  obtain ⟨R,hR,h⟩ := hS
  exact ⟨CompiledReduction.gameCode f R hR,CompiledReduction.gameCode_computable hC R hR,
    CompiledValue.reduction_promised hC R hR,
    fun e => (h e).trans (CompiledReduction.theorem_7_1_reduction hC R hR e).1.symm⟩

theorem entropy_promise_hard_of_compiler {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) : PromiseHard EntropyPerfect PromisedGame := by
  intro S hS
  obtain ⟨R,hR,h⟩ := hS
  exact ⟨CompiledReduction.gameCode f R hR,CompiledReduction.gameCode_computable hC R hR,
    CompiledValue.reduction_promised hC R hR,
    fun e => (h e).trans (CompiledReduction.theorem_7_1_reduction hC R hR e).2.1.symm⟩


/-- Theorem A from any compiler satisfying exactly the frozen specification. -/
theorem theoremA_of_tarski_of_compiler {f : ℕ → ℕ}
    (hC : Computable f ∧ ∀ code P,
      Encodable.decode (α := Presentation) code = some P → P.admissible →
        Compiler.Compiled P (f code) ∧ Compiler.ApproxCompiled P (f code))
    (hT : UpperRealArithmetic.TarskiDecision) : TheoremAStatement :=
  ⟨⟨Upper.spatial_sigmaTwo_of_tarski hT,spatial_hard_of_compiler hC⟩,
    ⟨Upper.entropy_sigmaTwo_of_tarski hT,entropy_hard_of_compiler hC⟩,
    spatial_promise_hard_of_compiler hC,entropy_promise_hard_of_compiler hC⟩

/-- Theorem A from the seven obligations, without the frozen chosen compiler. -/
theorem theoremA_of_tarski_of_obligations
    (hO : ∀ P, P.admissible → CompilerContract.Obligations P)
    (hT : UpperRealArithmetic.TarskiDecision) : TheoremAStatement := by
  obtain ⟨f,hC⟩ := CompilerContract.lemma_4_4_strong_of_obligations hO
  exact theoremA_of_tarski_of_compiler hC hT

end Sigma2

#print axioms Sigma2.theoremA_of_tarski_of_compiler
#print axioms Sigma2.theoremA_of_tarski_of_obligations
