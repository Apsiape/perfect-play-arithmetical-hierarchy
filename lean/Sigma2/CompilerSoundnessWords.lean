import Sigma2.CompilerSoundnessTriangles
import Sigma2.CompilerSoundnessWordClosure

/-! The actual retained words share the same qutrit frame and empty-word gauge. -/
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessWords
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessFrame CompilerSoundnessGraphs CompilerSoundnessJoints
  CompilerSoundnessTriangles CompilerSoundnessExtraction Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
  CompilerScaffold.wordRows

variable {P : Presentation}

def wordCorner (E : SupportedScaffold P) (w : Word) : Op :=
  graphBlock (projectionA P E.strategy E.supportA) w 0*
    star (graphBlock (projectionA P E.strategy E.supportA) [] 0)

theorem placement_rows (P : Presentation) (w : Word) (hw : w ∈ words P) :
    triangleRow w [] w ∈ rowList P ∧ triangleRow [] w w ∈ rowList P := by
  constructor
  · apply wordRow_mem P w hw
    change triangleRow w [] w ∈ CompilerScaffold.wordRows w
    unfold CompilerScaffold.wordRows
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_cons_self ..
  · apply wordRow_mem P w hw
    change triangleRow [] w w ∈ CompilerScaffold.wordRows w
    unfold CompilerScaffold.wordRows
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem placements (E : SupportedScaffold P) (w : Word) (hw : w ∈ words P) :
    graphBlock (projectionA P E.strategy E.supportA) w 0*
      graphBlock (projectionA P E.strategy E.supportA) [] 2=
        graphBlock (projectionA P E.strategy E.supportA) w 1 ∧
    graphBlock (projectionA P E.strategy E.supportA) [] 0*
      graphBlock (projectionA P E.strategy E.supportA) w 2=
        graphBlock (projectionA P E.strategy E.supportA) w 1 :=
  ⟨actual_triangle_composition E w [] w hw (empty_mem_words P) hw (placement_rows P w hw).1,
   actual_triangle_composition E [] w w (empty_mem_words P) hw hw (placement_rows P w hw).2⟩

theorem wordCorner_supported (E : SupportedScaffold P) (w : Word) :
    let f := fun i : Fin 3 => projectionA P E.strategy E.supportA (.frame i.val)
    FrameBlock f 0 0 (wordCorner E w) := by
  let F := projectionA P E.strategy E.supportA
  let f := fun i : Fin 3 => F (.frame i.val)
  have hw : FrameBlock f 0 1 (graphBlock F w 0) := by
    simpa [FrameBlock,pairs,f] using graph_frame_block F E.sharpA w 0
  have hq : FrameBlock f 0 1 (graphBlock F [] 0) := by
    simpa [FrameBlock,pairs,f] using graph_frame_block F E.sharpA [] 0
  have hs := block_star f (fun i => E.sharpA _) 0 1 _ hq
  constructor
  · change f 0*(graphBlock F w 0*star (graphBlock F [] 0))=_
    rw [← mul_assoc,hw.1]
    rfl
  · change (graphBlock F w 0*star (graphBlock F [] 0))*f 0=_
    rw [mul_assoc,hs.2]
    rfl

theorem wordCorner_unitary (E : SupportedScaffold P) (w : Word) (hw : w ∈ words P) :
    star (wordCorner E w)*wordCorner E w=projectionA P E.strategy E.supportA (.frame 0) ∧
      wordCorner E w*star (wordCorner E w)=projectionA P E.strategy E.supportA (.frame 0) := by
  let F := projectionA P E.strategy E.supportA
  let q := graphBlock F [] 0
  let z := graphBlock F w 0
  have hq : star q*q=F (.frame 1) ∧ q*star q=F (.frame 0) := E.graph [] (empty_mem_words P) 0
  have hz : star z*z=F (.frame 1) ∧ z*star z=F (.frame 0) := E.graph w hw 0
  have sq : q*F (.frame 1)=q := (graph_frame_block F E.sharpA [] 0).2
  have sz : z*F (.frame 1)=z := (graph_frame_block F E.sharpA w 0).2
  change star (z*star q)*(z*star q)=_ ∧ (z*star q)*star (z*star q)=_
  rw [star_mul,star_star]
  constructor
  · calc
      _=q*(star z*z)*star q := by noncomm_ring
      _=F (.frame 0) := by rw [hz.1,sq,hq.2]
  · calc
      _=z*(star q*q)*star z := by noncomm_ring
      _=F (.frame 0) := by rw [hq.1,sz,hz.2]

theorem wordCorner_empty (E : SupportedScaffold P) :
    wordCorner E []=projectionA P E.strategy E.supportA (.frame 0) :=
  (E.graph [] (empty_mem_words P) 0).2

theorem wordCorner_completion (E : SupportedScaffold P) (w : Word) (hw : w ∈ words P) :
    Unitary (wordCorner E w+(1-projectionA P E.strategy E.supportA (.frame 0))) := by
  let f := fun i : Fin 3 => projectionA P E.strategy E.supportA (.frame i.val)
  let V := wordCorner E w
  have hf : Projection (f 0) := E.sharpA (.frame 0)
  have hs : FrameBlock f 0 0 V := wordCorner_supported E w
  have hss := block_star f (fun i => E.sharpA _) 0 0 V hs
  have hu : star V*V=f 0 ∧ V*star V=f 0 := wordCorner_unitary E w hw
  have ht : star (V+(1-f 0))=star V+(1-f 0) := by
    rw [star_add V (1-f 0),star_sub (1:Op) (f 0),star_one,hf.1]
  constructor
  · change star (V+(1-f 0))*(V+(1-f 0))=1
    rw [ht]
    simp only [add_mul,mul_add,sub_mul,mul_sub,mul_one,one_mul,hu.1,
      hs.1,hs.2,hss.1,hss.2,hf.2]
    noncomm_ring
  · change (V+(1-f 0))*star (V+(1-f 0))=1
    rw [ht]
    simp only [add_mul,mul_add,sub_mul,mul_sub,mul_one,one_mul,hu.2,
      hs.1,hs.2,hss.1,hss.2,hf.2]
    noncomm_ring

theorem word12 (E : SupportedScaffold P) (w : Word) (hw : w ∈ words P) :
    let F := projectionA P E.strategy E.supportA
    graphBlock F w 2=star (graphBlock F [] 0)*graphBlock F w 0*graphBlock F [] 2 := by
  let F := projectionA P E.strategy E.supportA
  let q := graphBlock F [] 0
  let z := graphBlock F w 2
  have hq : star q*q=F (.frame 1) := (E.graph [] (empty_mem_words P) 0).1
  have hz : F (.frame 1)*z=z := (graph_frame_block F E.sharpA w 2).1
  calc
    z=F (.frame 1)*z := hz.symm
    _=(star q*q)*z := by rw [hq]
    _=star q*(q*z) := mul_assoc _ _ _
    _=star q*(graphBlock F w 0*graphBlock F [] 2) := by
      rw [(placements E w hw).2,← (placements E w hw).1]
    _=_ := (mul_assoc _ _ _).symm

/-- The same empty-word gauge decodes every submitted product triangle. -/
theorem wordCorner_composition (E : SupportedScaffold P)
    (u v w : Word) (hu : u ∈ words P) (hv : v ∈ words P) (hw : w ∈ words P)
    (htri : triangleRow u v w ∈ rowList P) :
    wordCorner E u*wordCorner E v=wordCorner E w := by
  let F := projectionA P E.strategy E.supportA
  let q := graphBlock F [] 0
  let r := graphBlock F [] 2
  have hr : r*star r=F (.frame 1) := (E.graph [] (empty_mem_words P) 2).2
  have sv : graphBlock F v 0*F (.frame 1)=graphBlock F v 0 := (graph_frame_block F E.sharpA v 0).2
  have sw : graphBlock F w 0*F (.frame 1)=graphBlock F w 0 := (graph_frame_block F E.sharpA w 0).2
  have hh := actual_triangle_composition E u v w hu hv hw htri
  rw [word12 E v hv] at hh
  have hl : (graphBlock F u 0*(star q*graphBlock F v 0*r))*star r*star q=
      wordCorner E u*wordCorner E v := by
    calc
      _=(graphBlock F u 0*star q)*(graphBlock F v 0*(r*star r))*star q := by noncomm_ring
      _=wordCorner E u*wordCorner E v := by rw [hr,sv]; rfl
  have hw' : graphBlock F w 1*star r*star q=wordCorner E w := by
    rw [← (placements E w hw).1]
    calc
      _=graphBlock F w 0*(r*star r)*star q := by noncomm_ring
      _=wordCorner E w := by rw [hr,sw]; rfl
  exact hl.symm.trans ((congrArg (fun X : Op => X*star r*star q) hh).trans hw')

#print axioms placements
#print axioms wordCorner_unitary
#print axioms wordCorner_completion
#print axioms wordCorner_composition
end Sigma2.CompilerSoundnessWords
