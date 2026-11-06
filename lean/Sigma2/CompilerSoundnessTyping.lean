import Sigma2.CompilerSoundnessSourceOperators

/-! Typing of the four returned decoders from the literal submitted rows. -/
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessTyping
open Compiler CompilerScaffold CompilerSoundnessExtraction CompilerSoundnessLift
  CompilerSoundnessDictionary CompilerSoundnessIntertwiners
  CompilerSoundnessLabels CompilerSoundnessSourceOperators Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

theorem corner_unitary_contraction (C U : Op) (hC : Projection C)
    (hU : star U*U=C) : Contraction U := by
  have hn : ‖C‖≤1 := IsStarProjection.norm_le C ⟨hC.2,hC.1⟩
  have hs : ‖U‖*‖U‖=‖C‖ := by rw [← CStarRing.norm_star_mul_self,hU]
  change ‖U‖≤1
  nlinarith [norm_nonneg U]

theorem decoder_positive (C U : Op) (hC : Projection C)
    (hU : star U*U=C) (hs : C*U=U ∧ U*C=U) :
    Positive ((1/4:ℂ) • ((2:ℂ) • C+U+star U)) ∧
    Positive (C-(1/4:ℂ) • ((2:ℂ) • C+U+star U)) := by
  have hstar : star U*C=star U := by
    simpa only [star_mul,hC.1] using congrArg (fun A : Op => star A) hs.1
  have hp : star (C+U)*(C+U)=(2:ℂ) • C+U+star U := by
    rw [PauliMatrixUnits.op_star_add,hC.1,add_mul,mul_add,mul_add,hC.2,hs.1,hstar,hU]
    module
  have hm : (1/4:ℂ) • (star (C-U)*(C-U))=C-(1/4:ℂ) • ((2:ℂ) • C+U+star U) := by
    rw [star_sub C U,hC.1,sub_mul,mul_sub,mul_sub,hC.2,hs.1,hstar,hU]
    module
  constructor
  · rw [← hp]
    exact (ContinuousLinearMap.isPositive_adjoint_comp_self (C+U)).smul_of_nonneg (by norm_num [Complex.le_def])
  · rw [← hm]
    exact (ContinuousLinearMap.isPositive_adjoint_comp_self (C-U)).smul_of_nonneg (by norm_num [Complex.le_def])

theorem decoder_projection (C U : Op) (hC : Projection C)
    (hU : star U*U=C) (hs : C*U=U ∧ U*C=U) (hsq : U*U=C) :
    Projection ((1/2:ℂ) • (C+U)) := by
  have hstar : star U*C=star U := by
    simpa only [star_mul,hC.1] using congrArg (fun A : Op => star A) hs.1
  have hself : star U=U := by
    calc
      _=star U*C := hstar.symm
      _=star U*(U*U) := by rw [hsq]
      _=U := by rw [← mul_assoc,hU,hs.1]
  constructor
  · rw [PauliMatrixUnits.op_star_smul,PauliMatrixUnits.op_star_add,hC.1,hself]
    norm_num
  · rw [smul_mul_smul_comm,add_mul,mul_add,mul_add,hC.2,hs.1,hs.2,hsq]
    module

theorem decoder_typed (C U V : Op) (t : LabelType) (hC : Projection C)
    (hU : star U*U=C ∧ U*star U=C) (hs : C*U=U ∧ U*C=U)
    (hV : t=.contraction → star V*V=C)
    (hsq : t=.projection → U*U=C) : TypedAt C (decoder C U V t) t := by
  cases t with
  | unitary => exact hU
  | projection => exact decoder_projection C U hC hU.1 hs (hsq rfl)
  | positive => exact decoder_positive C U hC hU.1 hs
  | contraction =>
    change ‖(1/2:ℂ) • (U+V)‖≤1
    have hu := corner_unitary_contraction C U hC hU.1
    have hv := corner_unitary_contraction C V hC (hV rfl)
    rw [norm_smul]
    norm_num only [norm_div,norm_one,Complex.norm_ofNat]
    calc
      _≤(1/2:ℝ)*(‖U‖+‖V‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
      _≤1 := by change ‖U‖≤1 at hu; change ‖V‖≤1 at hv; linarith

theorem projection_row_mem (P : Presentation) (r : Fin 5) (i : Fin P.types.length)
    (ht : P.types[i.val]=.projection) :
    sub (mul (copyAtom P r.val (encodingOffset P i.val))
      (copyAtom P r.val (encodingOffset P i.val))) one ∈ structuralPolynomials P := by
  have hi : P.types[i.val]?=some .projection := (List.getElem?_eq_getElem i.isLt).trans (congrArg some ht)
  have hm : sub (mul (copyAtom P r.val (encodingOffset P i.val))
      (copyAtom P r.val (encodingOffset P i.val))) one ∈
      (List.range 5).flatMap (fun r => (List.range P.types.length).filterMap (fun i =>
        if P.types[i]?=some .projection then some (sub (mul (copyAtom P r (encodingOffset P i))
          (copyAtom P r (encodingOffset P i))) one) else none)) := by
    apply List.mem_flatMap.mpr
    refine ⟨r.val,List.mem_range.mpr r.isLt,?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨i.val,List.mem_range.mpr i.isLt,by rw [if_pos hi]⟩
  simp only [structuralPolynomials,List.mem_append]
  tauto

theorem encoded_projection_square (E : SupportedScaffold P) (r : Fin 5)
    (i : Fin P.types.length) (ht : P.types[i.val]=.projection) :
    encoded E r.val (encodingOffset P i.val)*encoded E r.val (encodingOffset P i.val)=corner E r.val := by
  have hp := full_polynomial_equations E _ (show sub (mul (copyAtom P r.val (encodingOffset P i.val))
      (copyAtom P r.val (encodingOffset P i.val))) one ∈ polynomials P from by
    simp only [polynomials,List.mem_append]; exact Or.inl (projection_row_mem P r i ht))
  rw [fullValue_sub,fullValue_mul,fullValue_one] at hp
  have hsq : copy E r.val (encodingOffset P i.val)*copy E r.val (encodingOffset P i.val)=E.supportA := sub_eq_zero.mp hp
  have hc := (copy_commutes E r ⟨_,encoding_offset_lt P i⟩).eq
  change (corner E r.val*copy E r.val (encodingOffset P i.val))*(corner E r.val*copy E r.val (encodingOffset P i.val))=_
  calc
    _=corner E r.val*(copy E r.val (encodingOffset P i.val)*corner E r.val)*copy E r.val (encodingOffset P i.val) := by simp only [mul_assoc]
    _=(corner E r.val*corner E r.val)*(copy E r.val (encodingOffset P i.val)*copy E r.val (encodingOffset P i.val)) := by rw [← hc]; simp only [mul_assoc]
    _=corner E r.val := by rw [(corner_projection E _).2,hsq,(corner_supported E _).2]

theorem label_typed (E : SupportedScaffold P) (r : Fin 5) (i : Fin P.types.length) :
    TypedAt (corner E r.val) (label E r.val i.val) P.types[i.val] := by
  rw [label_formula E r i]
  apply decoder_typed _ _ _ _ (corner_projection E _) (encoded_unitary E r ⟨_,encoding_offset_lt P i⟩)
    (encoded_supported E r ⟨_,encoding_offset_lt P i⟩)
  · intro ht
    exact (encoded_unitary E r ⟨_,encoding_second_lt P i ht⟩).1
  · exact encoded_projection_square E r i

theorem returnedLabel_typed (E : SupportedScaffold P) (i : Fin P.types.length) :
    TypedAt (CompilerSoundnessSource.support E) (returnedLabel E i.val) P.types[i.val] := by
  rw [returnedLabel,if_pos i.isLt,source_eq]
  exact label_typed E 0 i

#print axioms returnedLabel_typed
end Sigma2.CompilerSoundnessTyping
