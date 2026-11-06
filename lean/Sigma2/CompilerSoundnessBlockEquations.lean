import Sigma2.CompilerSoundnessBlockSigns

/-! Evaluate the frozen block identity in the one extracted frame. -/
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessBlockEquations
open Compiler CompilerScaffold CompilerSoundnessExtraction CompilerSoundnessWordEvaluation
  CompilerSoundnessPolynomials CompilerSoundnessCopies
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def value (E : SupportedScaffold P) (p : Poly) : Op := evalPoly (unitaries E) p*frame E

theorem evalPoly_frame (E : SupportedScaffold P) (p : Poly) :
    Commute (frame E) (evalPoly (unitaries E) p) := by
  induction p with
  | nil => simp [evalPoly,Commute]
  | cons t p ih =>
    exact ((evalWord_frame E t.2).smul_right (t.1:ℂ)).add_right ih

theorem value_one (E : SupportedScaffold P) : value E one=frame E := by
  rw [value,eval_one,one_mul]
theorem value_append (E : SupportedScaffold P) (p q : Poly) :
    value E (p++q)=value E p+value E q := by
  simp only [value,evalPoly_append,add_mul]
theorem value_sub (E : SupportedScaffold P) (p q : Poly) :
    value E (sub p q)=value E p-value E q := by
  simp only [value,evalPoly_sub,sub_mul]
theorem value_mul (E : SupportedScaffold P) (p q : Poly) :
    value E (mul p q)=value E p*value E q := by
  change evalPoly (unitaries E) (mul p q)*frame E=_
  rw [evalPoly_mul]
  change _=(evalPoly (unitaries E) p*frame E)*(evalPoly (unitaries E) q*frame E)
  calc
    _=evalPoly (unitaries E) p*evalPoly (unitaries E) q*(frame E*frame E) := by
      rw [(E.sharpA _).2]
    _=evalPoly (unitaries E) p*(evalPoly (unitaries E) q*frame E)*frame E := by noncomm_ring
    _=evalPoly (unitaries E) p*(frame E*evalPoly (unitaries E) q)*frame E := by
      rw [(evalPoly_frame E q).eq]
    _=_ := by noncomm_ring

theorem value_adj (E : SupportedScaffold P) (p : Poly) :
    value E (adj p)=star (value E p) := by
  have ha (q : Poly) : evalPoly (unitaries E) (adj q)=star (evalPoly (unitaries E) q) := by
    induction q with
    | nil =>
      change (0:Op)=star (0:Op)
      exact (star_zero Op).symm
    | cons t q ih =>
      change (t.1:ℂ) • evalWord (unitaries E) (adjWord t.2)+evalPoly (unitaries E) (adj q)=
        star ((t.1:ℂ) • evalWord (unitaries E) t.2+evalPoly (unitaries E) q)
      rw [evalWord_adj,ih,star_add ((t.1:ℂ) • evalWord (unitaries E) t.2) (evalPoly (unitaries E) q),
        star_smul,star_ratCast]
  rw [value,ha,value,star_mul,(E.sharpA _).1]
  have hc := CompilerSoundnessBlockSigns.commute_adjoint _ _ (E.sharpA _).1 (evalPoly_frame E p)
  exact hc.eq.symm

theorem value_sum (E : SupportedScaffold P) (ps : List Poly) :
    value E (CompilerScaffold.sum ps)=(ps.map (value E)).sum := by
  induction ps with
  | nil => simp [value,CompilerScaffold.sum,evalPoly]
  | cons p ps ih =>
    change value E (p++CompilerScaffold.sum ps)=(value E p)+(ps.map (value E)).sum
    rw [value_append,ih]

theorem value_e (E : SupportedScaffold P) (r : Fin 5) :
    value E (e r.val)=sourceCorner E r.val := by
  have hi : cornerIndex r.val<25 := by
    have := r.isLt
    unfold cornerIndex
    split_ifs <;> omega
  exact eval_corner_frame E ⟨cornerIndex r.val,hi⟩

theorem block_structural_mem (P : Presentation) (g : Fin 4) (l : Fin (encodingCount P)) :
    sub (blockAtom P g.val l.val) (sub one (activity g.val) ++
      mul (e g.val) (copyAtom P g.val l.val) ++
      sum ((List.range 4).map (transportTerm P g.val l.val))) ∈ structuralPolynomials P := by
  have hm : sub (blockAtom P g.val l.val) (sub one (activity g.val) ++
      mul (e g.val) (copyAtom P g.val l.val) ++
      sum ((List.range 4).map (transportTerm P g.val l.val))) ∈
      (List.range 4).flatMap (fun g => (List.range (encodingCount P)).map (fun l =>
        sub (blockAtom P g l) (sub one (activity g) ++
          mul (e g) (copyAtom P g l) ++
          sum ((List.range 4).map (transportTerm P g l))))) :=
    List.mem_flatMap.mpr ⟨g.val,List.mem_range.mpr g.isLt,
      List.mem_map.mpr ⟨l.val,List.mem_range.mpr l.isLt,rfl⟩⟩
  simp only [structuralPolynomials,List.mem_append]
  tauto

/-- Every literal numbered block is the encoded source copy plus the four
literal axis-conjugated target copies, with the complement term intact. -/
theorem block_equation (E : SupportedScaffold P) (g : Fin 4) (l : Fin (encodingCount P)) :
    value E (blockAtom P g.val l.val)=
      frame E-value E (activity g.val)+
        value E (e g.val)*value E (copyAtom P g.val l.val)+
        ((List.range 4).map (fun k => value E (transportTerm P g.val l.val k))).sum := by
  have hp := structural_equations E _ (block_structural_mem P g l)
  change value E (sub (blockAtom P g.val l.val) _)=0 at hp
  rw [value_sub] at hp
  rw [sub_eq_zero.mp hp,value_append,value_append,value_sub,value_one,value_mul,value_sum,List.map_map]
  rfl

#print axioms value_mul
#print axioms value_adj
#print axioms block_equation
end Sigma2.CompilerSoundnessBlockEquations
