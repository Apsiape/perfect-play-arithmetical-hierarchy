import Sigma2.CompilerSoundnessRefinements

/-! The actual calibrated bridges preserve the extracted common frame and gauge. -/
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessBridgeFrame
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessBindings
  CompilerSoundnessGraphs CompilerSoundnessJoints CompilerSoundnessParameters
  CompilerSoundnessExtraction CompilerSoundnessRefinements Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def bridge (E : SupportedScaffold P) (g : Fin 4) : Op :=
  E.supportA*transportA E.strategy (fmsInstance P g)*E.supportA

def sign (E : SupportedScaffold P) (g : Fin 4) : Op :=
  E.supportA*(E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA 0)-
    E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA 1))*E.supportA

theorem normal_fms_reduces (E : SupportedScaffold P) (g : Fin 4) :
    flagA E.strategy (fmsInstance P g)*E.supportA=E.supportA*flagA E.strategy (fmsInstance P g) ∧
      magicA E.strategy (fmsInstance P g) 0*E.supportA=E.supportA*magicA E.strategy (fmsInstance P g) 0 := by
  obtain ⟨T,hT,hA,hM,_⟩ := conditional_pure_model E.strategy (fmsInstance P g) (E.conditional g)
  have hf := (SharpEvents.conditional_flag_sharp T (fmsInstance P g) hT E.densityA
    (hM E.densityA E.marginalA) E.supportA E.supportA_laws).1
  have hm := (SharpEvents.conditional_magic_sharp T (fmsInstance P g) hT E.densityA
    (hM E.densityA E.marginalA) E.supportA E.supportA_laws 0).1
  simpa only [flagA,magicA,normalOfPure,hA] using And.intro hf hm

theorem bridge_factor (E : SupportedScaffold P) (g : Fin 4) :
    bridge E g=projectionA P E.strategy E.supportA (.parameter (1+4*g.val))*sign E g*
      projectionA P E.strategy E.supportA (.parameter (cornerIndex g.val)) := by
  have hh := ActualCalibration.compressed_transport E.supportA (magicA E.strategy (fmsInstance P g) 0)
    (E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA 0)-
      E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA 1))
    (flagA E.strategy (fmsInstance P g)) E.supportA_laws.1
    (normal_fms_reduces E g).2 (normal_fms_reduces E g).1
  change (E.supportA*magicA E.strategy (fmsInstance P g) 0*E.supportA)*
    sign E g*(E.supportA*flagA E.strategy (fmsInstance P g)*E.supportA)=bridge E g at hh
  simpa only [magic_binding P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws,
    flag_binding P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws,
    Fin.val_zero,Nat.add_zero] using hh.symm

theorem refinement_commutes_sign (E : SupportedScaffold P) (g : Fin 4) (k : Fin (6+encodingCount P)) :
    Commute (projectionA P E.strategy E.supportA (refinementLabel P g.val k.val)) (sign E g) := by
  have hh := (actual_refinement E g k).2.2.1
  let L := E.supportA*E.strategy.measurements.alice (namedEvent P _ (refinementLabel_mem P g k)).x 1*E.supportA
  have hL : projectionA P E.strategy E.supportA (refinementLabel P g.val k.val)=L :=
    projectionA_of_mem P E.strategy E.supportA _ (refinementLabel_mem P g k)
  have hc (a : Fin 6) : Commute
      (projectionA P E.strategy E.supportA (refinementLabel P g.val k.val))
      (E.supportA*E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA a)*E.supportA) := by
    have ha := hh a
    change (E.supportA*E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA a)*E.supportA)*L=
      L*(E.supportA*E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA a)*E.supportA) at ha
    rw [← hL] at ha
    exact ha.symm
  have hs := (hc 0).sub_right (hc 1)
  simpa only [sign,mul_sub,sub_mul] using hs

theorem bridge_commutes_of_refinement (E : SupportedScaffold P) (g : Fin 4) (k : Fin (6+encodingCount P))
    (hf : Commute (projectionA P E.strategy E.supportA (refinementLabel P g.val k.val))
      (projectionA P E.strategy E.supportA (.parameter (cornerIndex g.val))))
    (hm : Commute (projectionA P E.strategy E.supportA (refinementLabel P g.val k.val))
      (projectionA P E.strategy E.supportA (.parameter (1+4*g.val)))) :
    Commute (projectionA P E.strategy E.supportA (refinementLabel P g.val k.val)) (bridge E g) := by
  rw [bridge_factor]
  exact (hm.mul_right (refinement_commutes_sign E g k)).mul_right hf

theorem frame_bridge (E : SupportedScaffold P) (g : Fin 4) (i : Fin 3) :
    Commute (projectionA P E.strategy E.supportA (.frame i.val)) (bridge E g) := by
  let k : Fin (6+encodingCount P) := ⟨i.val,by have := i.isLt; omega⟩
  have hk : refinementLabel P g.val k.val=.frame i.val := by simp [refinementLabel,k,i.isLt]
  rw [← hk]
  apply bridge_commutes_of_refinement E g k
  · rw [hk]
    exact (E.parameter_frame ⟨cornerIndex g.val,by
      have := g.isLt; unfold cornerIndex; split_ifs <;> omega⟩ i).symm
  · rw [hk]
    exact (E.parameter_frame ⟨1+4*g.val,by have := g.isLt; omega⟩ i).symm

theorem empty_graph_bridge (E : SupportedScaffold P) (g : Fin 4) (i : Fin 3) :
    Commute (projectionA P E.strategy E.supportA (.graph [] i.val 0)) (bridge E g) := by
  let k : Fin (6+encodingCount P) := ⟨3+i.val,by have := i.isLt; omega⟩
  have hk : refinementLabel P g.val k.val=.graph [] i.val 0 := by
    unfold refinementLabel
    rw [if_neg (by dsimp [k]; omega),if_pos (by dsimp [k]; have := i.isLt; omega)]
    congr 1
    dsimp [k]
    omega
  rw [← hk]
  apply bridge_commutes_of_refinement E g k
  · rw [hk]
    exact (parameter_graph P E.supportA (projectionA P E.strategy E.supportA) E.sharpA E.frame.2.1 E.rowsA
      ⟨cornerIndex g.val,by have := g.isLt; unfold cornerIndex; split_ifs <;> omega⟩ i).1.symm
  · rw [hk]
    exact (parameter_graph P E.supportA (projectionA P E.strategy E.supportA) E.sharpA E.frame.2.1 E.rowsA
      ⟨1+4*g.val,by have := g.isLt; omega⟩ i).1.symm

/-- No new frame or bridge is chosen: every original transport block commutes
with the common empty-word off-diagonal gauge. -/
theorem gauge_bridge (E : SupportedScaffold P) (g : Fin 4) (i : Fin 3) :
    Commute (bridge E g) (graphBlock (projectionA P E.strategy E.supportA) [] i.val) := by
  have hi := CompilerSoundnessJoints.pair_bounds i
  let a : Fin 3 := ⟨(pairs[i.val]?.getD (0,1)).1,hi.1⟩
  let b : Fin 3 := ⟨(pairs[i.val]?.getD (0,1)).2,hi.2.1⟩
  have ha := (frame_bridge E g a).symm
  have hb := (frame_bridge E g b).symm
  have hG := (empty_graph_bridge E g i).symm
  exact (ha.mul_right ((hG.smul_right (2:ℂ)).sub_right (ha.add_right hb))).mul_right hb

#print axioms normal_fms_reduces
#print axioms bridge_factor
#print axioms refinement_commutes_sign
#print axioms frame_bridge
#print axioms empty_graph_bridge
#print axioms gauge_bridge
end Sigma2.CompilerSoundnessBridgeFrame
