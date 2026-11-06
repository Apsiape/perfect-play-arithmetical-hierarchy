import Sigma2.CompilerApproxPrefixBase
import Sigma2.CompilerHonestRealization
import Sigma2.CompilerHonestDensityEntropy

/-! stop-rule diagnostic. This module leaves BaseObligation unchanged.
It records the precise additional Bob-entropy field needed to apply the frozen
RowCompleteness entropy clause to the very same base-strategy witness. It does
not assert either completeness proposition or a mathematical gap in the paper. -/
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerEntropyInterface
open Compiler CompilerScaffold CompilerApproxRows CompilerApproxDictionaryStrategy
  CompilerApproxPrefixBase CompilerApproxDictionaryEnergy

/-- The clock development's weighted-density theorem applies to the literal stage 5
oldDensity, including its actual weighted qutrit representation. -/
theorem oldDensity_finite_entropy {P : Presentation} (R : StructuralRealization P)
    (hR : FiniteDensityEntropy R.density) : FiniteDensityEntropy (oldDensity R) := by
  unfold oldDensity
  apply CompilerHonestDensityEntropy.weighted_finite_entropy 3
  exact CompilerHonestDensityEntropy.scaffold_finite_entropy R.density hR

/-- Proposed extension only. All five original base fields are retained, and
Bob's actual marginal has finite entropy whenever the input density does.
The final field is conditional, so no entropy assumption is imposed on inputs
whose density is not known to have finite entropy. -/
def BaseObligationE (P : Presentation) : Prop :=
  ∀ R : StructuralRealization P, ∃ S : NormalStrategy (preGame P).scenario,
    Perfect (preGame P) S ∧ NamedBinaryProjections (rows P) S ∧
    StructuralRowsHold P S ∧ MarginalA S (oldDensity R) ∧ NamedProjections P R S ∧
    (FiniteDensityEntropy R.density →
      ∃ hB : Density, MarginalB S hB ∧ FiniteDensityEntropy hB)

theorem base_of_baseE (P : Presentation) (hE : BaseObligationE P) : BaseObligation P := by
  intro R
  obtain ⟨S,hS,hN,hR,hm,hn,_⟩ := hE R
  exact ⟨S,hS,hN,hR,hm,hn⟩

/-- This is exactly the frozen two-marginal entropy input. Alice follows from
the existing density theorem; only the displayed Bob field is additional. -/
theorem finiteMarginalEntropy_of_bob {P : Presentation} (R : StructuralRealization P)
    (S : NormalStrategy (preGame P).scenario) (hm : MarginalA S (oldDensity R))
    (hR : FiniteDensityEntropy R.density)
    (hB : ∃ hB : Density, MarginalB S hB ∧ FiniteDensityEntropy hB) :
    FiniteMarginalEntropy S := by
  obtain ⟨hB,hmB,hEB⟩ := hB
  exact ⟨oldDensity R,hB,hm,hmB,oldDensity_finite_entropy R hR,hEB⟩

theorem entropy_witness_of_baseE (P : Presentation) (hE : BaseObligationE P)
    (R : StructuralRealization P) (hR : FiniteDensityEntropy R.density) :
    ∃ S : NormalStrategy (preGame P).scenario,
      Perfect (preGame P) S ∧ NamedBinaryProjections (rows P) S ∧
      StructuralRowsHold P S ∧ MarginalA S (oldDensity R) ∧ NamedProjections P R S ∧
      FiniteMarginalEntropy S := by
  obtain ⟨S,hS,hN,hs,hm,hn,hB⟩ := hE R
  exact ⟨S,hS,hN,hs,hm,hn,finiteMarginalEntropy_of_bob R S hm hR (hB hR)⟩

#print axioms CompilerHonestRealization.structural
#print axioms CompilerHonestRealization.application_residual_zero
#print axioms oldDensity_finite_entropy
#print axioms BaseObligationE
#print axioms base_of_baseE
#print axioms finiteMarginalEntropy_of_bob
#print axioms entropy_witness_of_baseE
#print BaseObligationE
#print FiniteMarginalEntropy
end Sigma2.CompilerEntropyInterface
