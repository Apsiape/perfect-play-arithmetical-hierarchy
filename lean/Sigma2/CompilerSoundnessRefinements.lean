import Sigma2.CompilerSoundnessPolynomials

/-! Every numbered refinement question instantiates the actual Lemma 4.2 API. -/
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessRefinements
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessBindings CompilerSoundnessExtraction Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

 def answerEquiv : (Fin 6 × Fin 2) ≃ Fin 12 where
  toFun az := ⟨2*az.1.val+az.2.val,by have := az.1.isLt; have := az.2.isLt; omega⟩
  invFun a := (⟨a.val/2,by have := a.isLt; omega⟩,⟨a.val%2,by omega⟩)
  left_inv az := by
    apply Prod.ext <;> apply Fin.ext
    · change (2*az.1.val+az.2.val)/2=az.1.val
      have := az.2.isLt
      omega
    · change (2*az.1.val+az.2.val)%2=az.2.val
      have := az.2.isLt
      omega
  right_inv a := by apply Fin.ext; change 2*(a.val/2)+a.val%2=a.val; omega

theorem sum_answers (A : Fin 12 → Op) :
    (∑ a : Fin 6,∑ z : Fin 2,A (answerEquiv (a,z)))=∑ b : Fin 12,A b := by
  have hh : (∑ az : Fin 6 × Fin 2,A (answerEquiv az))=∑ b : Fin 12,A b :=
    Fintype.sum_equiv answerEquiv _ _ (fun az => rfl)
  simpa only [Fintype.sum_prod_type] using hh

theorem refinementLabel_mem (P : Presentation) (g : Fin 4) (k : Fin (6+encodingCount P)) :
    refinementLabel P g.val k.val ∈ names P := by
  unfold refinementLabel
  split_ifs with h3 h6
  · exact frame_mem P ⟨k.val,h3⟩
  · have hh : ProjectionName.graph [] (k.val-3) 0 ∈
        (List.range 3).map (fun j => ProjectionName.graph [] j 0) :=
      List.mem_map.mpr ⟨k.val-3,List.mem_range.mpr (by omega),rfl⟩
    simp only [names,List.mem_dedup,List.mem_append]
    tauto
  · have hh : ProjectionName.graph [(33+5*encodingCount P+g.val*encodingCount P+(k.val-6),false)] 0 0 ∈
        (List.range 4).flatMap (fun j => (List.range (encodingCount P)).map (fun l =>
          ProjectionName.graph [(33+5*encodingCount P+j*encodingCount P+l,false)] 0 0)) := by
      exact List.mem_flatMap.mpr ⟨g.val,List.mem_range.mpr g.isLt,List.mem_map.mpr
        ⟨k.val-6,List.mem_range.mpr (by have := k.isLt; omega),rfl⟩⟩
    simp only [names,List.mem_dedup,List.mem_append]
    tauto

def refinementQuestion (P : Presentation) (g : Fin 4) (k : Fin (6+encodingCount P)) : QA (scenario P) :=
  ⟨(names P).length+20+g.val*(6+encodingCount P)+k.val,by
    have hg : g.val*(6+encodingCount P)≤3*(6+encodingCount P) :=
      Nat.mul_le_mul_right _ (by have := g.isLt; omega)
    have hk := k.isLt
    dsimp [scenario,refinementCount]
    omega⟩

theorem question_refinement (P : Presentation) (g : Fin 4) (k : Fin (6+encodingCount P)) :
    question P (refinementQuestion P g k).val=.refinement g.val k.val := by
  let d := 6+encodingCount P
  have hd : 0<d := by dsimp [d]; omega
  have hk : k.val<d := k.isLt
  have hg : g.val*d≤3*d := Nat.mul_le_mul_right _ (by have := g.isLt; omega)
  change question P ((names P).length+20+g.val*d+k.val)=_
  unfold question
  rw [if_neg (by omega),if_neg (by omega),if_pos (by dsimp [refinementCount]; dsimp [d] at *; omega)]
  have ho : (names P).length+20+g.val*d+k.val-(names P).length-20=g.val*d+k.val := by omega
  rw [ho]
  have hv : (g.val*d+k.val)/d=g.val := by
    rw [Nat.mul_comm g.val d,Nat.mul_add_div hd,Nat.div_eq_of_lt hk,Nat.add_zero]
  have hm : (g.val*d+k.val)%d=k.val := by
    rw [Nat.mul_comm g.val d,Nat.mul_add_mod,Nat.mod_eq_of_lt hk]
  exact congrArg₂ Question.refinement hv hm

theorem question_fms_alice (P : Presentation) (g : Fin 4) (x : Fin 5) :
    question P ((fmsInstance P g).qA x).val=.fms g.val x.val := by
  change question P ((names P).length+5*g.val+x.val)=_
  exact question_fms P g x

theorem question_fms_bob (P : Presentation) (g : Fin 4) (x : Fin 5) :
    question P ((fmsInstance P g).qB x).val=.fms g.val x.val := by
  change question P ((names P).length+5*g.val+x.val)=_
  exact question_fms P g x

theorem question_named_bob (P : Presentation) (n : ProjectionName) (hn : n ∈ names P) :
    question P (namedEvent P n hn).y.val=.binary n := by
  change question P (namedEvent P n hn).x.val=_
  exact question_named P n hn

def refinementInstance (P : Presentation) (g : Fin 4) (k : Fin (6+encodingCount P)) :
    LabelRefinementInstance (scenario P) (fmsInstance P g) where
  newA := refinementQuestion P g k
  newB := refinementQuestion P g k
  answerA a z := answerEquiv (a,z)
  answerB a z := answerEquiv (a,z)
  injectiveA := answerEquiv.injective
  injectiveB := answerEquiv.injective
  labelQA := (namedEvent P (refinementLabel P g.val k.val) (refinementLabel_mem P g k)).x
  labelQB := (namedEvent P (refinementLabel P g.val k.val) (refinementLabel_mem P g k)).y
  labelA := 1
  labelB := 1

theorem rule_true_reverse (P : Presentation) (q p : Question) (a b : ℕ)
    (hr : rule P q p a b=true) : directed P false p q b a=true := by
  simp only [rule,Bool.and_eq_true] at hr
  exact hr.2

/-- These are the actual numbered questions and the untouched opposite FMS questions. -/
theorem refinementPerfect {P : Presentation} (E : SupportedScaffold P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) :
    RefinementPerfect E.strategy (fmsInstance P g) (refinementInstance P g k) := by
  let F := refinementInstance P g k
  refine ⟨E.conditional g,?_,?_,?_,?_,?_,?_,?_⟩
  · change (∑ a : Fin 6,∑ z : Fin 2,E.strategy.measurements.alice (refinementQuestion P g k) (answerEquiv (a,z)))=1
    rw [sum_answers]
    exact E.strategy.measurements.alice_sum _
  · change (∑ a : Fin 6,∑ z : Fin 2,E.strategy.measurements.bob (refinementQuestion P g k) (answerEquiv (a,z)))=1
    rw [sum_answers]
    exact E.strategy.measurements.bob_sum _
  · intro y hy a z b hbad
    apply pre_rejected_probability P E.strategy E.perfect
    apply Bool.eq_false_iff.mpr
    intro hr
    change rule P (question P (refinementQuestion P g k).val)
      (question P ((fmsInstance P g).qB y).val) (2*a.val+z.val) b.val=true at hr
    rw [question_refinement,question_fms_bob] at hr
    have hh := rule_true_directed P _ _ _ _ hr
    have hv : (2*a.val+z.val)/2=a.val := by have := z.isLt; omega
    have hok : conditionalFmsRule 3 y.val a.val b.val=true := by simpa [directed,hy,hv] using hh
    rw [hbad] at hok
    contradiction
  · intro x hx a b z hbad
    apply pre_rejected_probability P E.strategy E.perfect
    apply Bool.eq_false_iff.mpr
    intro hr
    change rule P (question P ((fmsInstance P g).qA x).val)
      (question P (refinementQuestion P g k).val) a.val (2*b.val+z.val)=true at hr
    rw [question_fms_alice,question_refinement] at hr
    have hh := rule_true_reverse P _ _ _ _ hr
    have hv : (2*b.val+z.val)/2=b.val := by have := z.isLt; omega
    have hok : conditionalFmsRule x.val 3 a.val b.val=true := by simpa [directed,hx,hv] using hh
    rw [hbad] at hok
    contradiction
  · intro a z b hbad
    apply pre_rejected_probability P E.strategy E.perfect
    apply Bool.eq_false_iff.mpr
    intro hr
    change rule P (question P (refinementQuestion P g k).val)
      (question P (namedEvent P _ (refinementLabel_mem P g k)).y.val) (2*a.val+z.val) b.val=true at hr
    rw [question_refinement,question_named_bob] at hr
    have hh := rule_true_directed P _ _ _ _ hr
    have hv : (2*a.val+z.val)%2=z.val := by have := z.isLt; omega
    have hok : z.val=1 ↔ b.val=1 := by simpa [directed,hv] using hh
    apply hbad
    change z.val=1 ↔ b=(1:BB (scenario P))
    simp only [Fin.ext_iff]
    change z.val=1 ↔ _ = (1:ℕ)
    exact hok
  · intro a b z hbad
    apply pre_rejected_probability P E.strategy E.perfect
    apply Bool.eq_false_iff.mpr
    intro hr
    change rule P (question P (namedEvent P _ (refinementLabel_mem P g k)).x.val)
      (question P (refinementQuestion P g k).val) a.val (2*b.val+z.val)=true at hr
    rw [question_named,question_refinement] at hr
    have hh := rule_true_reverse P _ _ _ _ hr
    have hv : (2*b.val+z.val)%2=z.val := by have := z.isLt; omega
    have hok : z.val=1 ↔ a.val=1 := by simpa [directed,hv] using hh
    apply hbad
    change z.val=1 ↔ a=(1:AA (scenario P))
    simp only [Fin.ext_iff]
    change z.val=1 ↔ _ = (1:ℕ)
    exact hok
  · intro j hj
    obtain ⟨hA,hB,hmA,hmB,hmirror,hrA,hrB⟩ := E.rows_hold
    exact hmirror (nameIndex P _ (refinementLabel_mem P g k)) j hj

theorem actual_refinement {P : Presentation} (E : SupportedScaffold P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) :
    BridgeRefinementTransfer.RefinementConclusion E.strategy (fmsInstance P g)
      (refinementInstance P g k) E.supportA E.supportB :=
  ActualRefinement.actual_refinement E.strategy (fmsInstance P g) (refinementInstance P g k)
    (refinementPerfect E g k) E.densityA E.densityB E.marginalA E.marginalB
    E.supportA E.supportB E.supportA_laws E.supportB_laws

#print axioms refinementInstance
#print axioms refinementPerfect
#print axioms actual_refinement
end Sigma2.CompilerSoundnessRefinements
