import Sigma2.CompilerSoundnessBridgeCopies

/-! All four literal label decoders use the same fixed bridges, including adjoints. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessLabels
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessAxis CompilerSoundnessLift
  CompilerSoundnessDictionary CompilerSoundnessAxisCompression CompilerSoundnessBlockCompression
  CompilerSoundnessIntertwiners CompilerSoundnessTransport CompilerSoundnessBridgeCopies
  CompilerSoundnessCover CompilerSoundnessBridgeFrame
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def weight (t : LabelType) : ℕ := if t=.contraction then 2 else 1

theorem offset_bound (ts : List LabelType) (i : ℕ) (hi : i<ts.length) :
    ((ts.take i).map weight).sum+weight ts[i]≤(ts.map weight).sum := by
  induction ts generalizing i with
  | nil => simp at hi
  | cons t ts ih =>
    cases i with
    | zero => simp [weight]
    | succ i =>
      have h := ih i (by simpa using hi)
      simpa [List.take_succ_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using Nat.add_le_add_left h (weight t)

theorem encoding_bound (P : Presentation) (i : Fin P.types.length) :
    encodingOffset P i.val+(if P.types[i.val]=.contraction then 2 else 1)≤encodingCount P := by
  exact offset_bound P.types i.val i.isLt

theorem encoding_offset_lt (P : Presentation) (i : Fin P.types.length) :
    encodingOffset P i.val<encodingCount P := by
  have h := encoding_bound P i
  split_ifs at h <;> omega

theorem encoding_second_lt (P : Presentation) (i : Fin P.types.length)
    (ht : P.types[i.val]=.contraction) : encodingOffset P i.val+1<encodingCount P := by
  have h := encoding_bound P i
  rw [ht,if_pos rfl] at h
  omega

def decoder (C U V : Op) : LabelType → Op
  | .unitary => U
  | .projection => (1/2:ℂ) • (C+U)
  | .positive => (1/4:ℂ) • ((2:ℂ) • C+U+star U)
  | .contraction => (1/2:ℂ) • (U+V)

def label (E : SupportedScaffold P) (r i : ℕ) : Op := fullValue E (labelCopy P r i)

theorem encoded_star (E : SupportedScaffold P) (r : Fin 5) (l : Fin (encodingCount P)) :
    corner E r.val*star (copy E r.val l.val)=star (encoded E r.val l.val) := by
  have hc := congrArg (fun A : Op => star A) (copy_commutes E r l).eq
  have hC : star (corner E r.val)=corner E r.val := (corner_projection E _).1
  change corner E r.val*star (copy E r.val l.val)=star (corner E r.val*copy E r.val l.val)
  rw [star_mul,hC]
  simpa only [star_mul,hC] using hc.symm

theorem label_formula (E : SupportedScaffold P) (r : Fin 5) (i : Fin P.types.length) :
    label E r.val i.val=decoder (corner E r.val)
      (encoded E r.val (encodingOffset P i.val)) (encoded E r.val (encodingOffset P i.val+1)) P.types[i.val] := by
  have hi : P.types[i.val]?=some P.types[i.val] := List.getElem?_eq_getElem i.isLt
  have hu : fullValue E (copyAtom P r.val (encodingOffset P i.val))=copy E r.val (encodingOffset P i.val) := rfl
  have hv : fullValue E (copyAtom P r.val (encodingOffset P i.val+1))=copy E r.val (encodingOffset P i.val+1) := rfl
  unfold label labelCopy
  rw [hi]
  simp only [Option.getD_some]
  cases ht : P.types[i.val]
  · rw [fullValue_mul,fullValue_e,hu]
    rfl
  · rw [fullValue_mul,fullValue_e,fullValue_scale,fullValue_append,fullValue_one,hu]
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    change corner E r.val*((1/2:ℂ) • (E.supportA+copy E r.val (encodingOffset P i.val)))=_
    rw [mul_smul_comm,mul_add,(corner_supported E _).2]
    rfl
  · rw [fullValue_mul,fullValue_e,fullValue_scale,fullValue_append,fullValue_append,fullValue_adj,hu]
    have hs : fullValue E (scalar 2)=(2:ℂ) • E.supportA := by
      change spread E (evalPoly (CompilerSoundnessWordEvaluation.unitaries E) (scalar 2)*CompilerSoundnessCopies.frame E)=_
      have he : evalPoly (CompilerSoundnessWordEvaluation.unitaries E) (scalar 2)=(2:ℂ) • (1:Op) := by simp [evalPoly,scalar,evalWord]
      rw [he,smul_mul_assoc,one_mul,spread_smul,spread_frame]
    rw [hs]
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    change corner E r.val*((1/4:ℂ) • ((2:ℂ) • E.supportA+copy E r.val (encodingOffset P i.val)+star (copy E r.val (encodingOffset P i.val))))=_
    rw [mul_smul_comm,mul_add,mul_add,mul_smul_comm,(corner_supported E _).2,
      encoded_star E r ⟨_,encoding_offset_lt P i⟩]
    rfl
  · rw [fullValue_mul,fullValue_e,fullValue_scale,fullValue_append,hu,hv]
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
    change corner E r.val*((1/2:ℂ) • (copy E r.val (encodingOffset P i.val)+copy E r.val (encodingOffset P i.val+1)))=_
    rw [mul_smul_comm,mul_add]
    rfl

theorem decoder_transport (C D U V U' V' W : Op) (t : LabelType)
    (hc : D*W=W ∧ W*C=W) (hu : U'*W=W*U) (hus : star U'*W=W*star U)
    (hv : t=.contraction → V'*W=W*V) : decoder D U' V' t*W=W*decoder C U V t := by
  cases t with
  | unitary => exact hu
  | projection => simp only [decoder,smul_mul_assoc,mul_smul_comm,add_mul,mul_add,hc.1,hc.2,hu]
  | positive => simp only [decoder,smul_mul_assoc,mul_smul_comm,add_mul,mul_add,hc.1,hc.2,hu,hus]
  | contraction => simp only [decoder,smul_mul_assoc,mul_smul_comm,add_mul,mul_add,hu,hv rfl]

theorem decoder_adjoint_transport (C D U V U' V' W : Op) (t : LabelType)
    (hC : star C=C) (hD : star D=D) (hc : D*W=W ∧ W*C=W)
    (hu : U'*W=W*U) (hus : star U'*W=W*star U)
    (hvs : t=.contraction → star V'*W=W*star V) : star (decoder D U' V' t)*W=W*star (decoder C U V t) := by
  cases t with
  | unitary => exact hus
  | projection =>
    simp only [decoder,PauliMatrixUnits.op_star_smul,PauliMatrixUnits.op_star_add,hC,hD]
    norm_num only [star_div₀,star_one,star_ofNat]
    simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,hc.1,hc.2,hus]
  | positive =>
    simp only [decoder,PauliMatrixUnits.op_star_smul,PauliMatrixUnits.op_star_add,star_star,hC,hD]
    norm_num only [star_div₀,star_one,star_ofNat]
    simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,hc.1,hc.2,hu,hus]
  | contraction =>
    simp only [decoder,PauliMatrixUnits.op_star_smul,PauliMatrixUnits.op_star_add]
    norm_num only [star_div₀,star_one,star_ofNat]
    simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,hus,hvs rfl]

theorem label_intertwiner (E : SupportedScaffold P) (g : Fin 4) (i : Fin P.types.length) :
    label E (g.val+1) i.val*bridge E g=bridge E g*label E g.val i.val := by
  have hg0 : g.val<5 := by have := g.isLt; omega
  have hg1 : g.val+1<5 := by have := g.isLt; omega
  rw [label_formula E ⟨g.val+1,hg1⟩ i,label_formula E ⟨g.val,hg0⟩ i]
  apply decoder_transport _ _ _ _ _ _ _ _ (bridge_corner_support E g)
    (copy_intertwiner E g ⟨_,encoding_offset_lt P i⟩)
    (copy_adjoint_intertwiner E g ⟨_,encoding_offset_lt P i⟩)
  intro ht
  exact copy_intertwiner E g ⟨_,encoding_second_lt P i ht⟩

theorem label_adjoint_intertwiner (E : SupportedScaffold P) (g : Fin 4) (i : Fin P.types.length) :
    star (label E (g.val+1) i.val)*bridge E g=bridge E g*star (label E g.val i.val) := by
  have hg0 : g.val<5 := by have := g.isLt; omega
  have hg1 : g.val+1<5 := by have := g.isLt; omega
  rw [label_formula E ⟨g.val+1,hg1⟩ i,label_formula E ⟨g.val,hg0⟩ i]
  apply decoder_adjoint_transport _ _ _ _ _ _ _ _ (corner_projection E _).1 (corner_projection E _).1
    (bridge_corner_support E g) (copy_intertwiner E g ⟨_,encoding_offset_lt P i⟩)
    (copy_adjoint_intertwiner E g ⟨_,encoding_offset_lt P i⟩)
  intro ht
  exact copy_adjoint_intertwiner E g ⟨_,encoding_second_lt P i ht⟩


theorem decoder_supported (C U V : Op) (t : LabelType) (hC : Projection C)
    (hU : C*U=U ∧ U*C=U) (hV : t=.contraction → C*V=V ∧ V*C=V) :
    C*decoder C U V t=decoder C U V t ∧ decoder C U V t*C=decoder C U V t := by
  have hs : C*star U=star U ∧ star U*C=star U := by
    constructor
    · simpa only [star_mul,hC.1] using congrArg (fun A : Op => star A) hU.2
    · simpa only [star_mul,hC.1] using congrArg (fun A : Op => star A) hU.1
  cases t with
  | unitary => exact hU
  | projection => constructor <;> simp only [decoder,mul_smul_comm,smul_mul_assoc,mul_add,add_mul,hC.2,hU.1,hU.2]
  | positive => constructor <;> simp only [decoder,mul_smul_comm,smul_mul_assoc,mul_add,add_mul,hC.2,hU.1,hU.2,hs.1,hs.2]
  | contraction => constructor <;> simp only [decoder,mul_smul_comm,smul_mul_assoc,mul_add,add_mul,hU.1,hU.2,(hV rfl).1,(hV rfl).2]

theorem label_supported (E : SupportedScaffold P) (r : Fin 5) (i : Fin P.types.length) :
    corner E r.val*label E r.val i.val=label E r.val i.val ∧
      label E r.val i.val*corner E r.val=label E r.val i.val := by
  rw [label_formula E r i]
  apply decoder_supported _ _ _ _ (corner_projection E _) (encoded_supported E r ⟨_,encoding_offset_lt P i⟩)
  intro ht
  exact encoded_supported E r ⟨_,encoding_second_lt P i ht⟩

theorem label_chain (E : SupportedScaffold P) (i : Fin P.types.length) :
    label E 4 i.val*chain E=chain E*label E 0 i.val := by
  exact Compiler.same_bridge_transport (fun r : Fin 5 => fun i : Fin P.types.length => label E r.val i.val)
    (bridge E 0) (bridge E 1) (bridge E 2) (bridge E 3)
    (fun k => label_intertwiner E 0 k) (fun k => label_intertwiner E 1 k)
    (fun k => label_intertwiner E 2 k) (fun k => label_intertwiner E 3 k) i

theorem label_adjoint_chain (E : SupportedScaffold P) (i : Fin P.types.length) :
    star (label E 4 i.val)*chain E=chain E*star (label E 0 i.val) := by
  exact Compiler.same_bridge_transport (fun r : Fin 5 => fun i : Fin P.types.length => star (label E r.val i.val))
    (bridge E 0) (bridge E 1) (bridge E 2) (bridge E 3)
    (fun k => label_adjoint_intertwiner E 0 k) (fun k => label_adjoint_intertwiner E 1 k)
    (fun k => label_adjoint_intertwiner E 2 k) (fun k => label_adjoint_intertwiner E 3 k) i

#print axioms label_supported
#print axioms label_chain
#print axioms label_adjoint_chain

#print axioms label_formula
#print axioms label_intertwiner
#print axioms label_adjoint_intertwiner
end Sigma2.CompilerSoundnessLabels
