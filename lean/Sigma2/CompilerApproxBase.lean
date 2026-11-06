import Sigma2.CompilerApproxStrategy
set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace Sigma2.CompilerApproxBase
open Compiler CompilerScaffold CompilerApproxRows CompilerApproxStrategy
  CompilerApproxDictionaryEnergy CompilerApproxEvents

/-- Corrected-dictionary base interface, retaining the same strategy for all
six fields, including its conditional Bob-entropy witness. -/
def BaseObligation15 (P : Presentation) : Prop :=
  ∀ R : StructuralRealization P, ∃ S : NormalStrategy (preGame P).scenario,
    Perfect (preGame P) S ∧ NamedBinaryProjections (rows P) S ∧
    StructuralRowsHold P S ∧ MarginalA S (oldDensity R) ∧ NamedProjections15 P R S ∧
    (FiniteDensityEntropy R.density →
      ∃ hB : Density, MarginalB S hB ∧ FiniteDensityEntropy hB)

theorem clockObligation15_of_base15 (P : Presentation) (H : BaseObligation15 P) :
    ClockObligation15 P := by
  intro R
  obtain ⟨S,hS,hN,hR,hmarg,hnamed,_⟩ := H R
  exact honest_extension P R S hS hR hN hmarg hnamed

theorem approxCompiled_of_base15 (P : Presentation) (hP : P.admissible)
    (H : BaseObligation15 P) : ApproxCompiled P (codeFor P) :=
  approxCompiled_of_clock P hP (clockObligation15_of_base15 P H)

#print axioms BaseObligation15
#print axioms clockObligation15_of_base15
#print axioms approxCompiled_of_base15
end Sigma2.CompilerApproxBase
