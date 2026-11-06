import Sigma2.CompilerSoundnessDecoded

/-! Actual structural equations, supported copies, and the fixed sign refinements. -/
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessCopies
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessWordEvaluation CompilerSoundnessPolynomials CompilerSoundnessBridgeFrame
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

abbrev frame (E : SupportedScaffold P) : Op :=
  projectionA P E.strategy E.supportA (.frame 0)
abbrev parameter (E : SupportedScaffold P) (i : ℕ) : Op :=
  projectionA P E.strategy E.supportA (.parameter i)
def cornerCopy (E : SupportedScaffold P) (r l : ℕ) : Op :=
  unitaries E (33+r*encodingCount P+l)
def sourceCorner (E : SupportedScaffold P) (r : ℕ) : Op :=
  parameter E (cornerIndex r)*frame E

theorem eval_one (U : ℕ → Op) : evalPoly U one=1 := by
  simp [evalPoly,one,evalWord]
theorem eval_atom (U : ℕ → Op) (i : ℕ) : evalPoly U (atom i)=U i := by
  simp [evalPoly,atom,evalWord]

theorem eval_corner_frame (E : SupportedScaffold P) (i : Fin 25) :
    evalPoly (unitaries E) (corner i.val)*frame E=parameter E i.val*frame E := by
  rw [corner,evalPoly_scale,evalPoly_append,eval_one,eval_atom]
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat]
  rw [smul_mul_assoc,add_mul,one_mul,parameter_reflection E i]
  module

theorem sourceCorner_projection (E : SupportedScaffold P) (r : Fin 5) :
    Projection (sourceCorner E r.val) := by
  have hi : cornerIndex r.val<25 := by
    have := r.isLt
    unfold cornerIndex
    split_ifs <;> omega
  let A := parameter E (cornerIndex r.val)
  let F := frame E
  have hc : Commute A F := E.parameter_frame ⟨cornerIndex r.val,hi⟩ 0
  have hA : Projection A := E.sharpA _
  have hF : Projection F := E.sharpA _
  change Projection (A*F)
  constructor
  · rw [star_mul,hF.1,hA.1]
    exact hc.eq.symm
  · calc
      (A*F)*(A*F)=A*(F*A)*F := by simp only [mul_assoc]
      _=A*(A*F)*F := by rw [← hc.eq]
      _=(A*A)*(F*F) := by simp only [mul_assoc]
      _=A*F := by rw [hA.2,hF.2]

theorem copy_structural_mem (P : Presentation) (r : Fin 5) (l : Fin (encodingCount P)) :
    mul (sub (copyAtom P r.val l.val) one) (sub one (e r.val)) ∈ structuralPolynomials P := by
  have hm : mul (sub (copyAtom P r.val l.val) one) (sub one (e r.val)) ∈
      (List.range 5).flatMap (fun r => (List.range (encodingCount P)).map (fun l =>
        mul (sub (copyAtom P r l) one) (sub one (e r)))) :=
    List.mem_flatMap.mpr ⟨r.val,List.mem_range.mpr r.isLt,
      List.mem_map.mpr ⟨l.val,List.mem_range.mpr l.isLt,rfl⟩⟩
  simp only [structuralPolynomials,List.mem_append]
  tauto

/-- The actual submitted copy acts identically on the other sixteen corners,
inside the one common qutrit frame. -/
theorem copy_fix_complement (E : SupportedScaffold P) (r : Fin 5) (l : Fin (encodingCount P)) :
    cornerCopy E r.val l.val*(frame E-sourceCorner E r.val)=frame E-sourceCorner E r.val := by
  have hp := structural_equations E _ (copy_structural_mem P r l)
  rw [evalPoly_mul,evalPoly_sub,evalPoly_sub,copyAtom,eval_atom,eval_one] at hp
  have hi : cornerIndex r.val<25 := by
    have := r.isLt
    unfold cornerIndex
    split_ifs <;> omega
  have he := eval_corner_frame E ⟨cornerIndex r.val,hi⟩
  change evalPoly (unitaries E) (e r.val)*frame E=sourceCorner E r.val at he
  have hprod : (1-evalPoly (unitaries E) (e r.val))*frame E=frame E-sourceCorner E r.val := by
    rw [sub_mul,one_mul,he]
  change (cornerCopy E r.val l.val-1)*(1-evalPoly (unitaries E) (e r.val))*frame E=0 at hp
  rw [mul_assoc,hprod,sub_mul,one_mul] at hp
  exact sub_eq_zero.mp hp

/-- A unitary fixing a selfadjoint operator on the left also fixes it on the right. -/
theorem unitary_fix_right (U D : Op) (hU : Unitary U) (hD : star D=D)
    (h : U*D=D) : D*U=D := by
  have hs : D*star U=D := by simpa only [star_mul,hD] using congrArg (fun X : Op => star X) h
  calc
    D*U=(D*star U)*U := by rw [hs]
    _=D*(star U*U) := by noncomm_ring
    _=D := by rw [hU.1,mul_one]

theorem copy_commutes_source (E : SupportedScaffold P) (r : Fin 5) (l : Fin (encodingCount P)) :
    Commute (sourceCorner E r.val) (cornerCopy E r.val l.val) := by
  have hU := unitaries_unitary E (33+r.val*encodingCount P+l.val)
  have hf := unitaries_frame E (33+r.val*encodingCount P+l.val)
  have hc := sourceCorner_projection E r
  have hd : star (frame E-sourceCorner E r.val)=frame E-sourceCorner E r.val := by
    rw [star_sub (frame E) (sourceCorner E r.val),(E.sharpA _).1,hc.1]
  have hr := unitary_fix_right _ _ hU hd (copy_fix_complement E r l)
  change (frame E-sourceCorner E r.val)*cornerCopy E r.val l.val=_ at hr
  change frame E*cornerCopy E r.val l.val=cornerCopy E r.val l.val*frame E at hf
  change sourceCorner E r.val*cornerCopy E r.val l.val=cornerCopy E r.val l.val*sourceCorner E r.val
  have hl := copy_fix_complement E r l
  rw [sub_mul] at hr
  rw [mul_sub,← hf] at hl
  rw [sub_eq_add_neg] at hr hl
  exact neg_injective (add_left_cancel (hr.trans hl.symm))

/-- The source copy is an actual unitary in its decoded supported corner. -/
theorem copy_corner_unitary (E : SupportedScaffold P) (r : Fin 5) (l : Fin (encodingCount P)) :
    let C := sourceCorner E r.val
    let V := C*cornerCopy E r.val l.val
    star V*V=C ∧ V*star V=C := by
  let C := sourceCorner E r.val
  let U := cornerCopy E r.val l.val
  have hc : Projection C := sourceCorner_projection E r
  have hu : Unitary U := unitaries_unitary E _
  have hcu : C*U=U*C := (copy_commutes_source E r l).eq
  have hcs : star U*C=C*star U := by
    simpa only [star_mul,hc.1] using congrArg (fun X : Op => star X) hcu
  change star (C*U)*(C*U)=C ∧ (C*U)*star (C*U)=C
  rw [star_mul,hc.1]
  constructor
  · calc
      _=star U*(C*C)*U := by noncomm_ring
      _=star U*C*U := by rw [hc.2]
      _=C*(star U*U) := by rw [hcs]; noncomm_ring
      _=C := by rw [hu.1,mul_one]
  · calc
      _=C*(U*star U)*C := by noncomm_ring
      _=C := by rw [hu.2,mul_one,hc.2]

#print axioms eval_corner_frame
#print axioms sourceCorner_projection
#print axioms copy_fix_complement
#print axioms copy_commutes_source
#print axioms copy_corner_unitary
end Sigma2.CompilerSoundnessCopies
