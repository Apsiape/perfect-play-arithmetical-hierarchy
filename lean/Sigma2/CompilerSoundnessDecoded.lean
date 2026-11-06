import Sigma2.CompilerSoundnessBridgeFrame

/-! Concrete final-game extraction of the completed stage 24 decoding data. -/
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessDecoded
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessFrame
  CompilerSoundnessExtraction CompilerSoundnessCover CompilerSoundnessWordEvaluation
  CompilerSoundnessWords CompilerSoundnessPolynomials CompilerSoundnessRefinements CompilerSoundnessBridgeFrame
variable {P : Presentation}

theorem corner_partition (E : SupportedScaffold P) (i j : Fin 17) :
    projectionA P E.strategy E.supportA (.parameter i.val)*
      projectionA P E.strategy E.supportA (.parameter j.val)=
      if i=j then projectionA P E.strategy E.supportA (.parameter j.val) else 0 :=
  projection_partition E.supportA E.supportA_laws.1
    (fun k : Fin 17 => projectionA P E.strategy E.supportA (.parameter k.val))
    (fun k => E.sharpA _) (actual_cover P E.strategy E.perfect E.densityA E.marginalA
      E.supportA E.supportA_laws E.rowsA) i j

/-- All completed decoding facts use this one actual restricted strategy,
its original marginal supports, and the same four original calibrated blocks. -/
theorem decoded_of_final (P : Presentation) (T : NormalStrategy (finalGame P).scenario)
    (hT : Perfect (finalGame P) T) :
    ∃ E : SupportedScaffold P,
      Extends (RowGame.embedding (preGame P) (rows P)) E.strategy T ∧
      (FiniteMarginalEntropy E.strategy ↔ FiniteMarginalEntropy T) ∧
      (∑ i : Fin 17,projectionA P E.strategy E.supportA (.parameter i.val))=E.supportA ∧
      (trace (E.densityA.op*projectionA P E.strategy E.supportA (.parameter 0))).re=1/121 ∧
      (∀ i,Unitary (unitaries E i) ∧ Centralizes E.densityA.op (unitaries E i)) ∧
      (∀ w ∈ words P,evalWord (unitaries E) w*
        projectionA P E.strategy E.supportA (.frame 0)=wordCorner E w) ∧
      (∀ p ∈ polynomials P,evalPoly (unitaries E) p*
        projectionA P E.strategy E.supportA (.frame 0)=0) ∧
      (∀ g : Fin 4,∀ k : Fin (6+encodingCount P),
        BridgeRefinementTransfer.RefinementConclusion E.strategy (fmsInstance P g)
          (refinementInstance P g k) E.supportA E.supportB) ∧
      (∀ g : Fin 4,∀ i : Fin 3,
        Commute (bridge E g) (projectionA P E.strategy E.supportA (.frame i.val)) ∧
        Commute (bridge E g) (CompilerSoundnessGraphs.graphBlock
          (projectionA P E.strategy E.supportA) [] i.val)) := by
  obtain ⟨E,hExt,hEnt⟩ := of_final P T hT
  refine ⟨E,hExt,hEnt,actual_cover P E.strategy E.perfect E.densityA E.marginalA
    E.supportA E.supportA_laws E.rowsA,supported_source_mass E,
    fun i => ⟨unitaries_unitary E i,unitaries_central E i⟩,
    evalWord_retained E,polynomial_equations E,actual_refinement E,?_⟩
  intro g i
  exact ⟨(frame_bridge E g i).symm,gauge_bridge E g i⟩

#print axioms corner_partition
#print axioms decoded_of_final
end Sigma2.CompilerSoundnessDecoded
