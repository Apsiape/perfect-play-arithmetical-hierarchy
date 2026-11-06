import Sigma2.CompilerSoundnessAxis
import Sigma2.CompilerSoundnessLift

/-! The polynomial dictionary on the full original support. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessDictionary
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessBlockEquations CompilerSoundnessAxis
  CompilerSoundnessLift CompilerSoundnessPolynomials CompilerSoundnessWordEvaluation
  CompilerSoundnessBlockSigns CompilerSoundnessBridgeFrame
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

theorem fullValue_one (E : SupportedScaffold P) : fullValue E one=E.supportA := by
  rw [fullValue,value_one,spread_frame]

theorem fullValue_append (E : SupportedScaffold P) (p q : Poly) :
    fullValue E (p++q)=fullValue E p+fullValue E q := by
  rw [fullValue,value_append,spread_add]
  rfl

theorem fullValue_sub (E : SupportedScaffold P) (p q : Poly) :
    fullValue E (sub p q)=fullValue E p-fullValue E q := by
  rw [fullValue,value_sub,spread_sub]
  rfl

theorem fullValue_scale (E : SupportedScaffold P) (c : ℚ) (p : Poly) :
    fullValue E (scale c p)=(c:ℂ) • fullValue E p := by
  rw [fullValue,value_scale,spread_smul]
  rfl

theorem fullValue_adj (E : SupportedScaffold P) (p : Poly) :
    fullValue E (adj p)=star (fullValue E p) := by
  rw [fullValue,value_adj,spread_star]
  rfl

theorem fullValue_sum (E : SupportedScaffold P) (ps : List Poly) :
    fullValue E (CompilerScaffold.sum ps)=(ps.map (fullValue E)).sum := by
  induction ps with
  | nil => simp [CompilerScaffold.sum,fullValue,value,evalPoly,spread_zero]
  | cons p ps ih =>
    change fullValue E (p++CompilerScaffold.sum ps)=fullValue E p+(ps.map (fullValue E)).sum
    rw [fullValue_append,ih]

theorem fullValue_supported (E : SupportedScaffold P) (p : Poly) :
    E.supportA*fullValue E p=fullValue E p ∧ fullValue E p*E.supportA=fullValue E p :=
  spread_supported E _

theorem fullValue_expression (E : SupportedScaffold P) (r : Fin 5) (p : Expr) :
    fullValue E (expression P r.val p)=
      p.eval (parameter E (cornerIndex r.val)) (fun i => fullValue E (labelCopy P r.val i)) := by
  induction p with
  | scalar q => rw [expression,fullValue_scale,fullValue_e]; rfl
  | label i => rfl
  | add p q hp hq => rw [expression,fullValue_append,hp,hq]; rfl
  | mul p q hp hq => rw [expression,fullValue_mul,hp,hq]; rfl
  | adj p hp => rw [expression,fullValue_adj,hp]; rfl

theorem value_atom (E : SupportedScaffold P) (i : ℕ) :
    value E (atom i)=unitaries E i*frame E := by rw [value,eval_atom]

/-- Every numbered atom is unitary on the full original support. -/
theorem fullValue_atom_unitary (E : SupportedScaffold P) (i : ℕ) :
    let V := fullValue E (atom i)
    star V*V=E.supportA ∧ V*star V=E.supportA := by
  let F := frame E
  let U := unitaries E i
  have hF : Projection F := E.sharpA _
  have hU : Unitary U := unitaries_unitary E i
  have hc : F*U=U*F := (unitaries_frame E i).eq
  have hV : star (value E (atom i))*value E (atom i)=F ∧
      value E (atom i)*star (value E (atom i))=F := by
    rw [value_atom]
    change star (U*F)*(U*F)=F ∧ (U*F)*star (U*F)=F
    rw [star_mul,hF.1]
    constructor
    · calc
        _=F*(star U*U)*F := by simp only [mul_assoc]
        _=F := by rw [hU.1,mul_one,hF.2]
    · calc
        _=U*(F*F)*star U := by simp only [mul_assoc]
        _=F*(U*star U) := by rw [hF.2,← hc]; simp only [mul_assoc]
        _=F := by rw [hU.2,mul_one]
  have hs : star (value E (atom i))*frame E=star (value E (atom i)) := by
    have h := congrArg (fun X : Op => star X) (value_supported E (atom i)).1
    simpa only [star_mul,show star (frame E)=frame E from (E.sharpA _).1] using h
  change star (spread E (value E (atom i)))*spread E (value E (atom i))=_ ∧
    spread E (value E (atom i))*star (spread E (value E (atom i)))=_
  rw [← spread_star]
  constructor
  · rw [← spread_mul E _ _ hs,hV.1,spread_frame]
  · rw [← spread_mul E _ _ (value_supported E (atom i)).2,hV.2,spread_frame]

theorem full_copy_commutes (E : SupportedScaffold P) (r : Fin 5) (l : Fin (encodingCount P)) :
    Commute (parameter E (cornerIndex r.val)) (fullValue E (copyAtom P r.val l.val)) := by
  have hc := (copy_commutes_source E r l).eq
  have hv : sourceCorner E r.val*value E (copyAtom P r.val l.val)=
      value E (copyAtom P r.val l.val)*sourceCorner E r.val := by
    rw [copyAtom,value_atom]
    change sourceCorner E r.val*(cornerCopy E r.val l.val*frame E)=
      (cornerCopy E r.val l.val*frame E)*sourceCorner E r.val
    have hs : frame E*sourceCorner E r.val=sourceCorner E r.val := by simpa only [value_e E r] using (value_supported E (e r.val)).1
    have hr : sourceCorner E r.val*frame E=sourceCorner E r.val := by simpa only [value_e E r] using (value_supported E (e r.val)).2
    calc
      _=(sourceCorner E r.val*cornerCopy E r.val l.val)*frame E := (mul_assoc _ _ _).symm
      _=(cornerCopy E r.val l.val*sourceCorner E r.val)*frame E := by rw [hc]
      _=cornerCopy E r.val l.val*sourceCorner E r.val := by rw [mul_assoc,hr]
      _=cornerCopy E r.val l.val*(frame E*sourceCorner E r.val) := by rw [hs]
      _=_ := (mul_assoc _ _ _).symm
  have h := congrArg (spread E) hv
  have hs : sourceCorner E r.val*frame E=sourceCorner E r.val := by simpa only [value_e E r] using (value_supported E (e r.val)).2
  rw [spread_mul E _ _ hs,
    spread_mul E _ _ (value_supported E (copyAtom P r.val l.val)).2] at h
  have he : spread E (sourceCorner E r.val)=parameter E (cornerIndex r.val) := by
    rw [← value_e E r]
    exact fullValue_e E r
  rw [he] at h
  exact h

theorem spread_commutes (E : SupportedScaffold P) (A X : Op) (hA : star A=A)
    (hg : ∀ i,Commute A (gauge E i)) (hX : Commute A X) : Commute A (spread E X) := by
  change A*(∑ i : Fin 3,star (gauge E i)*X*gauge E i)=_
  rw [Finset.mul_sum,spread,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact (((commute_adjoint A _ hA (hg i)).mul_right hX).mul_right (hg i)).eq

/-- Every full numbered block still commutes with its original calibrated sign. -/
theorem full_block_commutes_sign (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    Commute (sign E g) (fullValue E (blockAtom P g.val l.val)) := by
  apply spread_commutes E _ _ (sign_selfadjoint E g)
  · intro i
    fin_cases i
    · exact frame_sign E g 0
    · simpa [CompilerSoundnessLift.gauge] using graphBlock_sign E g [] (empty_graph_sign E g 0)
    · change Commute (sign E g) (projectionA P E.strategy E.supportA (.frame 0)*
        ((2:ℂ) • projectionA P E.strategy E.supportA (.graph [] 1 0)-
          (projectionA P E.strategy E.supportA (.frame 0)+projectionA P E.strategy E.supportA (.frame 2)))*
            projectionA P E.strategy E.supportA (.frame 2))
      exact ((frame_sign E g 0).mul_right (((empty_graph_sign E g 1).smul_right (2:ℂ)).sub_right
        ((frame_sign E g 0).add_right (frame_sign E g 2)))).mul_right (frame_sign E g 2)
  · rw [blockAtom,value_atom]
    change Commute (sign E g) (blockUnitary E g.val l.val*frame E)
    exact (block_commutes_sign E g l).mul_right (frame_sign E g 0)

#print axioms fullValue_expression
#print axioms fullValue_atom_unitary
#print axioms full_copy_commutes
#print axioms full_block_commutes_sign
end Sigma2.CompilerSoundnessDictionary
