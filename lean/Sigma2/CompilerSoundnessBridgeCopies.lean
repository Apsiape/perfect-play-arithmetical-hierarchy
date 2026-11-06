import Sigma2.CompilerSoundnessTransport

/-! Every encoded label uses the same four original calibrated bridges. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessBridgeCopies
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessAxis CompilerSoundnessLift
  CompilerSoundnessDictionary CompilerSoundnessAxisCompression CompilerSoundnessBlockCompression
  CompilerSoundnessIntertwiners CompilerSoundnessTransport CompilerSoundnessCover CompilerSoundnessBridgeFrame
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

theorem block_source_edges (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    fullValue E (blockAtom P g.val l.val)*corner E g.val=encoded E g.val l.val ∧
      corner E g.val*fullValue E (blockAtom P g.val l.val)=encoded E g.val l.val := by
  apply unitary_compression_edges E.supportA _ _ _ (corner_projection E _) (corner_supported E _)
    (fullValue_atom_unitary E _) (block_source_sandwich E g l)
  exact encoded_unitary E ⟨g.val,by have := g.isLt; omega⟩ l

theorem block_target_edges (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    fullValue E (blockAtom P g.val l.val)*corner E (g.val+1)=encoded E (g.val+1) l.val ∧
      corner E (g.val+1)*fullValue E (blockAtom P g.val l.val)=encoded E (g.val+1) l.val := by
  apply unitary_compression_edges E.supportA _ _ _ (corner_projection E _) (corner_supported E _)
    (fullValue_atom_unitary E _) (block_target_sandwich E g l)
  exact encoded_unitary E ⟨g.val+1,by have := g.isLt; omega⟩ l

/-- The actual original calibrated bridge, for every numbered encoding. -/
theorem copy_intertwiner (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    encoded E (g.val+1) l.val*bridge E g=bridge E g*encoded E g.val l.val := by
  let D := fullValue E (blockAtom P g.val l.val)
  have hs := block_source_edges E g l
  have ht := block_target_edges E g l
  have hc : sign E g*D=D*sign E g := (full_block_commutes_sign E g l).eq
  have hw : bridge E g=corner E (g.val+1)*sign E g*corner E g.val := by
    simpa only [CompilerSoundnessIntertwiners.corner,next_index,parameter] using bridge_factor E g
  have hv := encoded_supported E ⟨g.val+1,by have := g.isLt; omega⟩ l
  have hv0 := encoded_supported E ⟨g.val,by have := g.isLt; omega⟩ l
  calc
    _=(encoded E (g.val+1) l.val*corner E (g.val+1))*sign E g*corner E g.val := by rw [hw]; simp only [mul_assoc]
    _=(corner E (g.val+1)*D)*sign E g*corner E g.val := by rw [hv.2,ht.2]
    _=corner E (g.val+1)*(D*sign E g)*corner E g.val := by simp only [mul_assoc]
    _=corner E (g.val+1)*(sign E g*D)*corner E g.val := by rw [← hc]
    _=corner E (g.val+1)*sign E g*encoded E g.val l.val := by
      rw [mul_assoc,mul_assoc,hs.1]
      simp only [mul_assoc]
    _=(corner E (g.val+1)*sign E g*corner E g.val)*encoded E g.val l.val := by
      have h0 : corner E g.val*encoded E g.val l.val=encoded E g.val l.val := hv0.1
      simp only [mul_assoc,h0]
    _=_ := by rw [← hw]

theorem bridge_corner_support (E : SupportedScaffold P) (g : Fin 4) :
    corner E (g.val+1)*bridge E g=bridge E g ∧ bridge E g*corner E g.val=bridge E g := by
  have hw : bridge E g=corner E (g.val+1)*sign E g*corner E g.val := by
    simpa only [CompilerSoundnessIntertwiners.corner,next_index,parameter] using bridge_factor E g
  constructor
  · rw [hw,← mul_assoc,← mul_assoc,(corner_projection E _).2]
  · rw [hw,mul_assoc,mul_assoc,(corner_projection E _).2]
    simp only [mul_assoc]

/-- Adjoint labels use the same actual bridge, rather than its adjoint or a new gauge. -/
theorem copy_adjoint_intertwiner (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    star (encoded E (g.val+1) l.val)*bridge E g=bridge E g*star (encoded E g.val l.val) := by
  have hs := encoded_unitary E ⟨g.val,by have := g.isLt; omega⟩ l
  have ht := encoded_unitary E ⟨g.val+1,by have := g.isLt; omega⟩ l
  have hw := bridge_corner_support E g
  calc
    _=star (encoded E (g.val+1) l.val)*(bridge E g*corner E g.val) := by rw [hw.2]
    _=star (encoded E (g.val+1) l.val)*(bridge E g*(encoded E g.val l.val*star (encoded E g.val l.val))) := by rw [hs.2]
    _=star (encoded E (g.val+1) l.val)*(bridge E g*encoded E g.val l.val)*star (encoded E g.val l.val) := by simp only [mul_assoc]
    _=star (encoded E (g.val+1) l.val)*(encoded E (g.val+1) l.val*bridge E g)*star (encoded E g.val l.val) := by rw [copy_intertwiner E g l]
    _=(star (encoded E (g.val+1) l.val)*encoded E (g.val+1) l.val)*bridge E g*star (encoded E g.val l.val) := by simp only [mul_assoc]
    _=_ := by rw [ht.1,hw.1]

def chain (E : SupportedScaffold P) : Op := bridge E 3*bridge E 2*bridge E 1*bridge E 0

theorem copy_chain (E : SupportedScaffold P) (l : Fin (encodingCount P)) :
    encoded E 4 l.val*chain E=chain E*encoded E 0 l.val := by
  exact Compiler.same_bridge_transport (fun r : Fin 5 => fun l : Fin (encodingCount P) => encoded E r.val l.val)
    (bridge E 0) (bridge E 1) (bridge E 2) (bridge E 3)
    (fun k => copy_intertwiner E 0 k) (fun k => copy_intertwiner E 1 k)
    (fun k => copy_intertwiner E 2 k) (fun k => copy_intertwiner E 3 k) l

theorem copy_adjoint_chain (E : SupportedScaffold P) (l : Fin (encodingCount P)) :
    star (encoded E 4 l.val)*chain E=chain E*star (encoded E 0 l.val) := by
  exact Compiler.same_bridge_transport (fun r : Fin 5 => fun l : Fin (encodingCount P) => star (encoded E r.val l.val))
    (bridge E 0) (bridge E 1) (bridge E 2) (bridge E 3)
    (fun k => copy_adjoint_intertwiner E 0 k) (fun k => copy_adjoint_intertwiner E 1 k)
    (fun k => copy_adjoint_intertwiner E 2 k) (fun k => copy_adjoint_intertwiner E 3 k) l

#print axioms copy_intertwiner
#print axioms copy_adjoint_intertwiner
#print axioms copy_chain
#print axioms copy_adjoint_chain
end Sigma2.CompilerSoundnessBridgeCopies
