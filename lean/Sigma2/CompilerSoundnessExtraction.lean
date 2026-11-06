import Sigma2.CompilerSoundnessParameters

/-! A single concrete extraction from codeFor, retaining the original ensemble
and actual marginal supports. This stops short of NormalRealization: the corner
cover and word/transport assembly are separate remaining obligations. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessExtraction
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessFrame CompilerSoundnessGraphs CompilerSoundnessParameters Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

structure SupportedScaffold (P : Presentation) where
  strategy : NormalStrategy (scenario P)
  perfect : Perfect (preGame P) strategy
  densityA : Density
  densityB : Density
  supportA : Op
  supportB : Op
  marginalA : MarginalA strategy densityA
  marginalB : MarginalB strategy densityB
  supportA_laws : SupportOf densityA supportA
  supportB_laws : SupportOf densityB supportB
  rows_hold : RowsHold (rows P) strategy
  rowsA : ∀ r ∈ rowList P,evalRow supportA (projectionA P strategy supportA) r=0
  rowsB : ∀ r ∈ rowList P,evalRow supportB (projectionB P strategy supportB) r=0
  conditional : ∀ g : Fin 4,ConditionalPerfect strategy (fmsInstance P g)

namespace SupportedScaffold
variable {P : Presentation} (E : SupportedScaffold P)

theorem sharpA (n : ProjectionName) : Projection (projectionA P E.strategy E.supportA n) :=
  CompilerSoundnessNames.sharpA P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws n

theorem sharpB (n : ProjectionName) : Projection (projectionB P E.strategy E.supportB n) :=
  CompilerSoundnessNames.sharpB P E.strategy E.perfect E.densityB E.marginalB E.supportB E.supportB_laws n

theorem frame :
    (∑ i : Fin 3,projectionA P E.strategy E.supportA (.frame i.val))=E.supportA ∧
      (∀ i j : Fin 3,projectionA P E.strategy E.supportA (.frame i.val)*
        projectionA P E.strategy E.supportA (.frame j.val)=
        if i=j then projectionA P E.strategy E.supportA (.frame j.val) else 0) ∧
      (∀ i : Fin 3,Centralizes E.densityA.op (projectionA P E.strategy E.supportA (.frame i.val))) :=
  actual_frame P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws E.rowsA

theorem parameter_frame (p : Fin 25) (i : Fin 3) :
    Commute (projectionA P E.strategy E.supportA (.parameter p.val))
      (projectionA P E.strategy E.supportA (.frame i.val)) :=
  parameter_frame_commutes P E.strategy E.perfect E.densityA E.marginalA
    E.supportA E.supportA_laws E.rowsA p i

theorem graph (w : Word) (hw : w ∈ words P) (k : Fin 3) :
    star (graphBlock (projectionA P E.strategy E.supportA) w k.val)*
        graphBlock (projectionA P E.strategy E.supportA) w k.val=
      projectionA P E.strategy E.supportA (.frame (pairs[k.val]?.getD (0,1)).2) ∧
      graphBlock (projectionA P E.strategy E.supportA) w k.val*
        star (graphBlock (projectionA P E.strategy E.supportA) w k.val)=
      projectionA P E.strategy E.supportA (.frame (pairs[k.val]?.getD (0,1)).1) :=
  actual_graph_isometry P E.strategy E.perfect E.densityA E.marginalA
    E.supportA E.supportA_laws E.rowsA w hw k

theorem bridge (g : Fin 4) : BridgeConclusion E.strategy (fmsInstance P g) E.densityA E.supportA :=
  CompilerSoundnessPadding.actual_bridge P E.strategy E.perfect g
    E.densityA E.marginalA E.supportA E.supportA_laws

theorem trace_recurrence (g k : Fin 4) :
    trace (E.densityA.op*projectionA P E.strategy E.supportA (.parameter (1+4*g.val+k.val)))=
      (2:ℂ)*trace (E.densityA.op*projectionA P E.strategy E.supportA (.parameter (cornerIndex g.val))) :=
  named_trace_recurrence P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws g k

end SupportedScaffold

/-- All objects and laws in the bundle come from this final-game strategy. -/
theorem of_final (P : Presentation) (T : NormalStrategy (finalGame P).scenario)
    (hT : Perfect (finalGame P) T) :
    ∃ E : SupportedScaffold P,
      Extends (RowGame.embedding (preGame P) (rows P)) E.strategy T ∧
        (FiniteMarginalEntropy E.strategy ↔ FiniteMarginalEntropy T) := by
  obtain ⟨S,hS,hR,hN,hC,hExt,hEnt⟩ := CompilerSoundnessSupport.from_final P T hT
  obtain ⟨hA,hB,eA,eB,hmA,hmB,heA,heB,hrA,hrB⟩ := decoded_rows P S hR
  exact ⟨⟨S,hS,hA,hB,eA,eB,hmA,hmB,heA,heB,hR,hrA,hrB,hC⟩,hExt,hEnt⟩

/-- The same supported extraction at the actual frozen GameTable code. -/
theorem of_codeFor (P : Presentation) (G : Game)
    (hG : decodeGame (codeFor P)=some G) (hT : HasPerfect G) :
    Nonempty (SupportedScaffold P) := by
  have heq : G=finalGame P := Option.some.inj (hG.symm.trans (decode_codeFor P))
  subst G
  obtain ⟨T,hT⟩ := hT
  obtain ⟨E,_,_⟩ := of_final P T hT
  exact ⟨E⟩

#print axioms SupportedScaffold.frame
#print axioms SupportedScaffold.parameter_frame
#print axioms SupportedScaffold.graph
#print axioms SupportedScaffold.bridge
#print axioms SupportedScaffold.trace_recurrence
#print axioms of_final
#print axioms of_codeFor
end Sigma2.CompilerSoundnessExtraction
