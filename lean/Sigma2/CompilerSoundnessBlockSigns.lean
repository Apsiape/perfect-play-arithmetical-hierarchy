import Sigma2.CompilerSoundnessCopies

/-! The actual block-label refinements commute with the fixed original sign.
No label-label commutation or replacement bridge is used. -/
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessBlockSigns
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessGraphs
  CompilerSoundnessExtraction CompilerSoundnessRefinements CompilerSoundnessWords
  CompilerSoundnessWordEvaluation CompilerSoundnessBridgeFrame
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def blockUnitary (E : SupportedScaffold P) (g l : ℕ) : Op :=
  unitaries E (33+5*encodingCount P+g*encodingCount P+l)

theorem sign_selfadjoint (E : SupportedScaffold P) (g : Fin 4) :
    star (sign E g)=sign E g := by
  let A := E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA 0)
  let B := E.strategy.measurements.alice ((fmsInstance P g).qA 3) ((fmsInstance P g).aA 1)
  have hs := E.supportA_laws.1.1
  have h0 : star A=A := (E.strategy.measurements.alice_pos _ _).isSelfAdjoint.star_eq
  have h1 : star B=B := (E.strategy.measurements.alice_pos _ _).isSelfAdjoint.star_eq
  have hd : star (A-B)=A-B := by rw [star_sub A B,h0,h1]
  change star (E.supportA*(A-B)*E.supportA)=E.supportA*(A-B)*E.supportA
  rw [star_mul,star_mul,hs,hd]
  simp only [mul_assoc]

theorem commute_adjoint (A B : Op) (hA : star A=A) (h : Commute A B) :
    Commute A (star B) := by
  have hh := congrArg (fun X : Op => star X) h.eq
  change A*star B=star B*A
  simpa only [star_mul,hA] using hh.symm

theorem frame_sign (E : SupportedScaffold P) (g : Fin 4) (i : Fin 3) :
    Commute (sign E g) (projectionA P E.strategy E.supportA (.frame i.val)) := by
  let k : Fin (6+encodingCount P) := ⟨i.val,by have := i.isLt; omega⟩
  have hk : refinementLabel P g.val k.val=.frame i.val := by simp [refinementLabel,k,i.isLt]
  have hh := refinement_commutes_sign E g k
  rw [hk] at hh
  exact hh.symm

theorem empty_graph_sign (E : SupportedScaffold P) (g : Fin 4) (i : Fin 3) :
    Commute (sign E g) (projectionA P E.strategy E.supportA (.graph [] i.val 0)) := by
  let k : Fin (6+encodingCount P) := ⟨3+i.val,by have := i.isLt; omega⟩
  have hk : refinementLabel P g.val k.val=.graph [] i.val 0 := by
    unfold refinementLabel
    rw [if_neg (by dsimp [k]; omega),if_pos (by dsimp [k]; have := i.isLt; omega)]
    congr 1
    dsimp [k]
    omega
  have hh := refinement_commutes_sign E g k
  rw [hk] at hh
  exact hh.symm

theorem block_graph_sign (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    Commute (sign E g) (projectionA P E.strategy E.supportA
      (.graph [(33+5*encodingCount P+g.val*encodingCount P+l.val,false)] 0 0)) := by
  let k : Fin (6+encodingCount P) := ⟨6+l.val,by have := l.isLt; omega⟩
  have hk : refinementLabel P g.val k.val=
      .graph [(33+5*encodingCount P+g.val*encodingCount P+l.val,false)] 0 0 := by
    unfold refinementLabel
    rw [if_neg (by dsimp [k]; omega),if_neg (by dsimp [k]; omega)]
    simp [k]
  have hh := refinement_commutes_sign E g k
  rw [hk] at hh
  exact hh.symm

theorem graphBlock_sign (E : SupportedScaffold P) (g : Fin 4) (w : Word)
    (h : Commute (sign E g) (projectionA P E.strategy E.supportA (.graph w 0 0))) :
    Commute (sign E g) (graphBlock (projectionA P E.strategy E.supportA) w 0) := by
  change Commute (sign E g) (projectionA P E.strategy E.supportA (.frame 0)*
    ((2:ℂ) • projectionA P E.strategy E.supportA (.graph w 0 0)-
      (projectionA P E.strategy E.supportA (.frame 0)+
        projectionA P E.strategy E.supportA (.frame 1)))*
          projectionA P E.strategy E.supportA (.frame 1))
  exact ((frame_sign E g 0).mul_right ((h.smul_right (2:ℂ)).sub_right
    ((frame_sign E g 0).add_right (frame_sign E g 1)))).mul_right (frame_sign E g 1)

/-- This is the same numbered block atom as in the structural block equation. -/
theorem block_commutes_sign (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    Commute (sign E g) (blockUnitary E g.val l.val) := by
  have hq := graphBlock_sign E g [] (empty_graph_sign E g 0)
  have hs := commute_adjoint _ _ (sign_selfadjoint E g) hq
  have hb := graphBlock_sign E g _ (block_graph_sign E g l)
  have hw : Commute (sign E g) (wordCorner E
      [(33+5*encodingCount P+g.val*encodingCount P+l.val,false)]) := hb.mul_right hs
  unfold blockUnitary unitaries
  split_ifs
  · exact hw.add_right ((Commute.one_right _).sub_right (frame_sign E g 0))
  · exact Commute.one_right _

theorem block_adjoint_commutes_sign (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    Commute (sign E g) (star (blockUnitary E g.val l.val)) :=
  commute_adjoint _ _ (sign_selfadjoint E g) (block_commutes_sign E g l)

#print axioms sign_selfadjoint
#print axioms frame_sign
#print axioms empty_graph_sign
#print axioms block_graph_sign
#print axioms block_commutes_sign
#print axioms block_adjoint_commutes_sign
end Sigma2.CompilerSoundnessBlockSigns
