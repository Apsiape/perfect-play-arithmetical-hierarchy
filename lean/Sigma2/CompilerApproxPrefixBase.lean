import Sigma2.CompilerApproxDictionaryStrategy

set_option backward.isDefEq.respectTransparency.types true
noncomputable section
namespace Sigma2.CompilerApproxPrefixBase
open Compiler CompilerScaffold CompilerEventLoss CompilerApproxDictionaryIndex CompilerApproxDictionaryEnergy
  CompilerApproxRows CompilerApproxDictionaryStrategy CompilerApproxDictionaryEvents

/-- The restriction is precisely the prefix before the application rows. -/
theorem nonapplication_iff_prefix (P : Presentation) (r : Fin (rows P).rowCount) :
    ¬ applicationRow P r ↔ r.val<(rowsBefore P).length := by
  rw [applicationRow,rowList_length,Nat.add_sub_cancel_right,not_le]

/-- Equivalently, no application row index is retained. -/
theorem nonapplication_iff_not_index (P : Presentation) (r : Fin (rows P).rowCount) :
    ¬ applicationRow P r ↔ ¬ ∃ j,rowIndex P j=r := by
  constructor
  · intro hr ⟨j,hj⟩
    exact hr (hj ▸ rowIndex_application P j)
  · intro hr ha
    exact hr (application_index P r ha)

/-- The exact remaining clock development obligation: only a base strategy, with its
actual marginal and numbered named-projection action. No application equation,
final-game strategy, numerical probability or loss estimate is assumed. -/
def BaseObligation (P : Presentation) : Prop :=
  ∀ R : StructuralRealization P, ∃ S : NormalStrategy (preGame P).scenario,
    Perfect (preGame P) S ∧ NamedBinaryProjections (rows P) S ∧
    StructuralRowsHold P S ∧ MarginalA S (oldDensity R) ∧ NamedProjections P R S

theorem clockObligation_of_base (P : Presentation) (H : BaseObligation P) :
    ClockObligation P := by
  intro R
  obtain ⟨S,hS,hN,hR,hmarg,hnamed⟩ := H R
  exact honest_extension P R S hS hR hN hmarg hnamed

theorem approxCompiled_of_base (P : Presentation) (hP : P.admissible) (H : BaseObligation P) :
    ApproxCompiled P (codeFor P) :=
  approxCompiled_of_clock P hP (clockObligation_of_base P H)

#print axioms nonapplication_iff_prefix
#print axioms nonapplication_iff_not_index
#print axioms BaseObligation
#print axioms clockObligation_of_base
#print axioms approxCompiled_of_base
end Sigma2.CompilerApproxPrefixBase
