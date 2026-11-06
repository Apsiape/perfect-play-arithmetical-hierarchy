import Sigma2.RowCompletenessComplete
import Sigma2.RowSoundnessComplete

noncomputable section
namespace Sigma2.RowCompleteness
open Compiler

theorem boolean_rows (G : Game) (R : Rows G.scenario) :
    ∃ (G' : Game) (E : ScenarioEmbedding G.scenario G'.scenario),
      (∀ T, Perfect G' T → ∃ S, Perfect G S ∧ Extends E S T ∧ RowsHold R S) ∧
      (∀ S, Perfect G S → RowsHold R S → NamedBinaryProjections R S →
        ∃ T, Perfect G' T ∧ Extends E S T ∧
          (FiniteMarginalEntropy S → FiniteMarginalEntropy T)) := by
  refine ⟨RowGame.game G R,RowGame.embedding G R,?_,?_⟩
  · intro T hT
    have hs := RowSoundness.soundness G R T hT
    exact ⟨RowRestriction.restrict G R T,hs.1,hs.2.1,hs.2.2.1⟩
  · intro S hS hR hN
    exact completeness G R S hS hR hN

#print axioms boolean_rows
end Sigma2.RowCompleteness
