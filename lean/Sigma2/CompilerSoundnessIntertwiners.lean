import Sigma2.CompilerSoundnessBlockCompression

/-! Full source/target copies in the literal block equation. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessIntertwiners
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessBlockEquations CompilerSoundnessAxis
  CompilerSoundnessLift CompilerSoundnessDictionary CompilerSoundnessAxisCompression
  CompilerSoundnessBlockCompression CompilerSoundnessCover CompilerSoundnessBridgeFrame
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def copy (E : SupportedScaffold P) (r l : ℕ) : Op := fullValue E (copyAtom P r l)
def corner (E : SupportedScaffold P) (r : ℕ) : Op := parameter E (cornerIndex r)
def encoded (E : SupportedScaffold P) (r l : ℕ) : Op := corner E r*copy E r l

theorem next_index (g : ℕ) : cornerIndex (g+1)=1+4*g := by
  rw [cornerIndex,if_neg (by omega)]
  omega

theorem corner_projection (E : SupportedScaffold P) (r : ℕ) : Projection (corner E r) := E.sharpA _

theorem corner_supported (E : SupportedScaffold P) (r : ℕ) :
    E.supportA*corner E r=corner E r ∧ corner E r*E.supportA=corner E r :=
  projectionA_supported P E.strategy E.supportA E.supportA_laws.1 _

theorem copy_unitary (E : SupportedScaffold P) (r l : ℕ) :
    star (copy E r l)*copy E r l=E.supportA ∧ copy E r l*star (copy E r l)=E.supportA :=
  fullValue_atom_unitary E _

theorem copy_commutes (E : SupportedScaffold P) (r : Fin 5) (l : Fin (encodingCount P)) :
    Commute (corner E r.val) (copy E r.val l.val) := full_copy_commutes E r l

theorem encoded_supported (E : SupportedScaffold P) (r : Fin 5) (l : Fin (encodingCount P)) :
    corner E r.val*encoded E r.val l.val=encoded E r.val l.val ∧
      encoded E r.val l.val*corner E r.val=encoded E r.val l.val := by
  have hc := (copy_commutes E r l).eq
  constructor
  · change corner E r.val*(corner E r.val*copy E r.val l.val)=_
    rw [← mul_assoc,(corner_projection E r.val).2]
    rfl
  · change (corner E r.val*copy E r.val l.val)*corner E r.val=_
    rw [mul_assoc,← hc,← mul_assoc,(corner_projection E r.val).2]
    rfl

theorem encoded_unitary (E : SupportedScaffold P) (r : Fin 5) (l : Fin (encodingCount P)) :
    star (encoded E r.val l.val)*encoded E r.val l.val=corner E r.val ∧
      encoded E r.val l.val*star (encoded E r.val l.val)=corner E r.val := by
  let C := corner E r.val
  let U := copy E r.val l.val
  have hC : Projection C := corner_projection E r.val
  have hU := copy_unitary E r.val l.val
  have hc : C*U=U*C := (copy_commutes E r l).eq
  have hcs : star U*C=C*star U := by
    simpa only [star_mul,hC.1] using congrArg (fun A : Op => star A) hc
  change star (C*U)*(C*U)=C ∧ (C*U)*star (C*U)=C
  rw [star_mul,hC.1]
  constructor
  · calc
      _=star U*(C*C)*U := by simp only [mul_assoc]
      _=C*(star U*U) := by rw [hC.2,hcs]; simp only [mul_assoc]
      _=C := by rw [hU.1,(corner_supported E r.val).2]
  · calc
      _=C*(U*star U)*C := by simp only [mul_assoc]
      _=C := by rw [hU.2,(corner_supported E r.val).2,hC.2]

theorem corners_orthogonal (E : SupportedScaffold P) (g : Fin 4) :
    corner E g.val*corner E (g.val+1)=0 ∧ corner E (g.val+1)*corner E g.val=0 := by
  have h0 : cornerIndex g.val<17 := by have := g.isLt; unfold cornerIndex; split_ifs <;> omega
  have h1 : cornerIndex (g.val+1)<17 := by rw [next_index]; have := g.isLt; omega
  have hn : (⟨cornerIndex g.val,h0⟩ : Fin 17)≠⟨cornerIndex (g.val+1),h1⟩ := by
    intro he
    have hv := congrArg Fin.val he
    change cornerIndex g.val=cornerIndex (g.val+1) at hv
    rw [next_index] at hv
    have := g.isLt
    unfold cornerIndex at hv
    split_ifs at hv <;> omega
  constructor
  · exact (CompilerSoundnessDecoded.corner_partition E ⟨_,h0⟩ ⟨_,h1⟩).trans (if_neg hn)
  · exact (CompilerSoundnessDecoded.corner_partition E ⟨_,h1⟩ ⟨_,h0⟩).trans (if_neg (Ne.symm hn))

/-- This is exactly the frozen structural block, on the full original support. -/
theorem literal_block (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    fullValue E (blockAtom P g.val l.val)=E.supportA-corner E g.val-magicSupport E g+
      encoded E g.val l.val+
      ((List.range 4).map (fun k => axisWord E g k*encoded E (g.val+1) l.val*star (axisWord E g k))).sum := by
  have hp := full_polynomial_equations E _ (show sub (blockAtom P g.val l.val)
      (sub one (activity g.val) ++ mul (e g.val) (copyAtom P g.val l.val) ++
        CompilerScaffold.sum ((List.range 4).map (transportTerm P g.val l.val))) ∈ polynomials P from by
    simp only [polynomials,List.mem_append]; exact Or.inl (block_structural_mem P g l))
  rw [fullValue_sub] at hp
  rw [sub_eq_zero.mp hp,fullValue_append,fullValue_append,fullValue_sub,fullValue_one,
    activity,fullValue_append,fullValue_e E ⟨g.val,by have := g.isLt; omega⟩,fullValue_magic,
    fullValue_mul,fullValue_e E ⟨g.val,by have := g.isLt; omega⟩,fullValue_sum,List.map_map]
  have hterms : (List.range 4).map (fun x => fullValue E (transportTerm P g.val l.val x))=
      (List.range 4).map (fun x => axisWord E g x*encoded E (g.val+1) l.val*star (axisWord E g x)) := by
    apply List.map_congr_left
    intro k _
    rw [fullValue_transportTerm]
    rfl
  simp only [Function.comp_def]
  rw [hterms]
  change E.supportA-(corner E g.val+magicSupport E g)+encoded E g.val l.val+_=_
  module

/-- The unitary block's two one-sided corner identities follow from its two
unitary sandwiches, with no extra invariance assumption. -/
theorem unitary_compression_edges (e C D V : Op) (hC : Projection C)
    (hs : e*C=C ∧ C*e=C) (hD : star D*D=e ∧ D*star D=e)
    (hv : C*D*C=V) (hV : star V*V=C ∧ V*star V=C) :
    D*C=V ∧ C*D=V := by
  have hb : star (D*C)*(D*C)=C := by
    rw [star_mul,hC.1]
    calc
      _=C*(star D*D)*C := by simp only [mul_assoc]
      _=C := by rw [hD.1,hs.2,hC.2]
  have hv0 : C*(D*C)=V := by simpa only [mul_assoc] using hv
  have hh : star (C*(D*C))*(C*(D*C))=star (D*C)*(D*C) := by
    rw [hv0,hV.1,hb]
  have hl := saturated_compression C (D*C) hC hh
  have hbs : star (star D*C)*(star D*C)=C := by
    rw [star_mul,hC.1,star_star]
    calc
      _=C*(D*star D)*C := by simp only [mul_assoc]
      _=C := by rw [hD.2,hs.2,hC.2]
  have hva : C*star D*C=star V := by
    have h := congrArg (fun A : Op => star A) hv
    simpa only [star_mul,hC.1,mul_assoc] using h
  have hva0 : C*(star D*C)=star V := by simpa only [mul_assoc] using hva
  have hhs : star (C*(star D*C))*(C*(star D*C))=star (star D*C)*(star D*C) := by
    rw [hva0,star_star,hV.2,hbs]
  have hr := congrArg (fun A : Op => star A) (saturated_compression C (star D*C) hC hhs)
  simp only [star_mul,hC.1,star_star] at hr
  refine ⟨?_,?_⟩
  · calc
      _=C*(D*C) := hl.symm
      _=V := by rw [← mul_assoc,hv]
  · calc
      _=C*D*C := by simpa only [mul_assoc] using hr.symm
      _=V := hv

#print axioms encoded_unitary
#print axioms literal_block
#print axioms unitary_compression_edges
end Sigma2.CompilerSoundnessIntertwiners
