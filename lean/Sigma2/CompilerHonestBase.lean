import Sigma2.CompilerHonestRows
import Sigma2.CompilerApproxBase

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerHonestBase
open Compiler CompilerScaffold CompilerApproxRows CompilerApproxStrategy CompilerApproxDictionaryEnergy

theorem base15 (P : Presentation) (R : StructuralRealization P) :
    Perfect (preGame P) (CompilerHonestRefinementsCorrect.strategy R) ∧
    NamedBinaryProjections (rows P) (CompilerHonestRefinementsCorrect.strategy R) ∧
    StructuralRowsHold P (CompilerHonestRefinementsCorrect.strategy R) ∧
    MarginalA (CompilerHonestRefinementsCorrect.strategy R) (oldDensity R) ∧
    NamedProjections15 P R (CompilerHonestRefinementsCorrect.strategy R) ∧
    (FiniteDensityEntropy R.density → ∃ hB : Density,
      MarginalB (CompilerHonestRefinementsCorrect.strategy R) hB ∧ FiniteDensityEntropy hB) := by
  obtain ⟨hS,hN,hR,hm,hn⟩ := CompilerHonestRows.base15 P R
  refine ⟨hS,hN,hR,hm,hn,?_⟩
  intro hh
  obtain ⟨hA,hB,hmA,hmB,hfA,hfB⟩ := CompilerHonestEntropyCorrect.strategy_finite_entropy R hh
  exact ⟨hB,hmB,hfB⟩

/-- An exact instance of the compiler development's actual corrected base interface. -/
theorem baseObligation15 (P : Presentation) : CompilerApproxBase.BaseObligation15 P := by
  intro R
  exact ⟨CompilerHonestRefinementsCorrect.strategy R,base15 P R⟩

#print axioms base15
#print axioms baseObligation15
end Sigma2.CompilerHonestBase
