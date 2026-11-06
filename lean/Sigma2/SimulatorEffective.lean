import Sigma2.SimulatorEffectiveKernel
import Sigma2.SimulatorFixedTable

noncomputable section
namespace Sigma2.SimulatorEffective
open Turing Sigma2.Tree Sigma2.Reduction Sigma2.SimulatorNumbered Sigma2.SimulatorParameterCoding

/-- The standard-seed verifier family has an explicit computable transition
compiler: one fixed verifier, finite parameter counters, and fixed-order symbols. -/
theorem effective_program (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ e, ProgramCorrect R e (decodeAutomaton (f e)) := by
  classical
  obtain ⟨Q, fQ, iQ, dQ, M, hM⟩ := correct_family R hR
  letI := fQ
  letI := iQ
  letI := dQ
  letI : Primcodable Q := Primcodable.ofEquiv (Fin (Fintype.card Q)) (Fintype.equivFin Q)
  letI : Primcodable SimulatorMachine.TapeAlphabet :=
    Primcodable.ofEquiv (Fin (Fintype.card SimulatorMachine.TapeAlphabet))
      (Fintype.equivFin SimulatorMachine.TapeAlphabet)
  exact SimulatorUniform.effective_of_uniform R
    (family M SimulatorStandard.unaryBody SimulatorStandard.unaryBottom SimulatorPair.separator
      (Coding.fixed SimulatorMachine.TapeAlphabet) (Coding.fixed Q)) hM
    (size_primrec M _ _ _ _ _).to_comp
    (SimulatorEffectiveKernel.localEntry_primrec M _ _ _).to_comp

#print axioms effective_program
end Sigma2.SimulatorEffective
