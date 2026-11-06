import Sigma2.RowSupportedRows

noncomputable section
namespace Sigma2.RowSoundness
open Compiler RowGame Preliminaries

/-- All RowsHold clauses for the exact old restriction, using the original
    supplied marginal densities for both supported row equations. -/
theorem rows_hold (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (hT : Perfect (game G R) T) :
    RowsHold R (RowRestriction.restrict G R T) := by
  obtain ⟨hA,hB,hmA,hmB⟩ := marginals_exist T
  obtain ⟨P,hP⟩ := support_exists hA
  obtain ⟨Q,hQ⟩ := support_exists hB
  exact ⟨hA,hB,hmA,hmB,component_mirrors G R T hT,
    fun r => RowScalar.supported_row_equation false G R T hT hA hmA P hP r,
    fun r => RowScalar.supported_row_equation true G R T hT hB hmB Q hQ r⟩

/-- Concrete simultaneous soundness: perfection, the original correlations,
    all rational row equations, and named binary projections, on one restriction. -/
theorem soundness (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (hT : Perfect (game G R) T) :
    Perfect G (RowRestriction.restrict G R T) ∧
      Extends (embedding G R) (RowRestriction.restrict G R T) T ∧
      RowsHold R (RowRestriction.restrict G R T) ∧
      NamedBinaryProjections R (RowRestriction.restrict G R T) :=
  ⟨RowRestriction.perfect G R T hT,RowRestriction.restriction_extends G R T hT,
    rows_hold G R T hT,RowRestriction.named G R T hT⟩

#print axioms rows_hold
#print axioms soundness
end Sigma2.RowSoundness