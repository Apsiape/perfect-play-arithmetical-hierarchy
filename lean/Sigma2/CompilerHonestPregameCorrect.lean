import Sigma2.CompilerHonestBindingsCorrect
import Sigma2.CompilerHonestDecodeCorrect

/-! Full pregame perfection for the realization-only honest strategy. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 1000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerHonestPregameCorrect
open Compiler CompilerScaffold CompilerHonestRefinementsCorrect CompilerHonestDecodeCorrect
  CompilerHonestBindingsCorrect CompilerProjectionDictionary CompilerHonestState
  CompilerHonestFMSLift CompilerHonestCentralizer CompilerHonestRefinementCommute CoefficientOperator
  RowCompleteness TensorLifts
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

def event {P : Presentation} (R : StructuralRealization P) (q p : Question) (a b : Fin 12) : AB :=
  (left ((localPartition R false q).effect a)*right ((localPartition R true p).effect b))
    (vector (density R.density))

theorem local_binary_value {P : Presentation} (R : StructuralRealization P) (bob : Bool)
    (n : ProjectionName) (a : Fin 12) (ha : a.val<2) :
    (localPartition R bob (.binary n)).effect a=
      (Partition.binary (if bob then transpose (CompilerOrientedProjections.projection R n) else CompilerOrientedProjections.projection R n)
        (by cases bob <;> first | exact (CompilerOrientedProjections.projection_projective R n).1 | exact (transpose_projection _ (CompilerOrientedProjections.projection_projective R n)).1)
        (by cases bob <;> first | exact (CompilerOrientedProjections.projection_projective R n).2 | exact (transpose_projection _ (CompilerOrientedProjections.projection_projective R n)).2)).effect
      (decide (a.val=1)) := by
  cases bob
  · exact binary_value _ (CompilerOrientedProjections.projection_projective R n) a ha
  · exact binary_value _ (transpose_projection _ (CompilerOrientedProjections.projection_projective R n)) a ha

theorem answer_decode (a : Fin 12) (ha : a.val<2) : answer (decide (a.val=1))=a.val := by
  simp only [answer,CompilerHonestBindings.answer,Bool.decide_iff]
  split_ifs <;> omega

theorem directed_A_zero {P : Presentation} (R : StructuralRealization P) (q p : Question)
    (hq : WellFormed P q) (hp : WellFormed P p) (a b : Fin 12)
    (ha : valid q a.val=true) (hb : valid p b.val=true)
    (hr : directed P true q p a.val b.val=false) : event R q p a b=0 := by
  cases q <;> cases p <;> simp only [directed,Bool.true_eq_false,Bool.false_eq_true,Bool.true_eq,ite_true,ite_false] at hr
  case fms.binary g x n =>
    obtain ⟨hg,hx⟩ := hq
    have ha6 : a.val<6 := by simpa only [valid,decide_eq_true_eq] using ha
    have hb2 : b.val<2 := by simpa only [valid,decide_eq_true_eq] using hb
    unfold event
    rw [fms_value R false ⟨g,hg⟩ ⟨x,hx⟩ a ha6,local_binary_value R true n b hb2]
    have hz : bindingVector R false ⟨g,hg⟩ ⟨x,hx⟩ n ⟨a.val,ha6⟩ (decide (b.val=1))=0 := by
      by_contra hne
      have h := binding_accepts R false ⟨g,hg⟩ ⟨x,hx⟩ n ⟨a.val,ha6⟩ (decide (b.val=1)) hne
      rw [answer_decode b hb2] at h
      exact Bool.noConfusion (h.symm.trans hr)
    exact hz
  case refinement.binary g k n =>
    obtain ⟨hg,hk⟩ := hq
    have hb2 : b.val<2 := by simpa only [valid,decide_eq_true_eq] using hb
    by_cases hn : n=refinementLabel P g k
    · rw [if_pos hn,decide_eq_false_iff_not] at hr
      subst n
      unfold event
      rw [refinement_value R false ⟨g,hg⟩ ⟨k,hk⟩,local_binary_value R true _ b hb2]
      exact alice_label_rejection R ⟨g,hg⟩ ⟨k,hk⟩ a (decide (b.val=1)) (by simpa only [decide_eq_true_eq] using hr)
    · simp only [if_neg hn,Bool.true_eq_false] at hr
  case refinement.fms g k h y =>
    obtain ⟨hg,hk⟩ := hq
    obtain ⟨hh,hy⟩ := hp
    have hb6 : b.val<6 := by simpa only [valid,decide_eq_true_eq] using hb
    split_ifs at hr with he
    rcases he with ⟨rfl,_⟩
    unfold event
    rw [refinement_value R false ⟨g,hg⟩ ⟨k,hk⟩,fms_value R true ⟨g,hg⟩ ⟨y,hy⟩ b hb6]
    exact alice_rejection R ⟨g,hg⟩ ⟨k,hk⟩ ⟨y,hy⟩ a ⟨b.val,hb6⟩ hr

theorem directed_B_zero {P : Presentation} (R : StructuralRealization P) (q p : Question)
    (hq : WellFormed P q) (hp : WellFormed P p) (a b : Fin 12)
    (ha : valid q a.val=true) (hb : valid p b.val=true)
    (hr : directed P false q p a.val b.val=false) : event R p q b a=0 := by
  cases q <;> cases p <;> simp only [directed,Bool.true_eq_false,Bool.false_eq_true,Bool.true_eq,ite_true,ite_false] at hr
  case fms.binary g x n =>
    obtain ⟨hg,hx⟩ := hq
    have ha6 : a.val<6 := by simpa only [valid,decide_eq_true_eq] using ha
    have hb2 : b.val<2 := by simpa only [valid,decide_eq_true_eq] using hb
    unfold event
    rw [local_binary_value R false n b hb2,fms_value R true ⟨g,hg⟩ ⟨x,hx⟩ a ha6]
    have hz : bindingVector R true ⟨g,hg⟩ ⟨x,hx⟩ n ⟨a.val,ha6⟩ (decide (b.val=1))=0 := by
      by_contra hne
      have h := binding_accepts R true ⟨g,hg⟩ ⟨x,hx⟩ n ⟨a.val,ha6⟩ (decide (b.val=1)) hne
      rw [answer_decode b hb2] at h
      exact Bool.noConfusion (h.symm.trans hr)
    exact hz
  case refinement.binary g k n =>
    obtain ⟨hg,hk⟩ := hq
    have hb2 : b.val<2 := by simpa only [valid,decide_eq_true_eq] using hb
    by_cases hn : n=refinementLabel P g k
    · rw [if_pos hn,decide_eq_false_iff_not] at hr
      subst n
      unfold event
      rw [local_binary_value R false _ b hb2,refinement_value R true ⟨g,hg⟩ ⟨k,hk⟩]
      exact bob_label_rejection R ⟨g,hg⟩ ⟨k,hk⟩ (decide (b.val=1)) a (by simpa only [decide_eq_true_eq] using hr)
    · simp only [if_neg hn,Bool.true_eq_false] at hr
  case refinement.fms g k h y =>
    obtain ⟨hg,hk⟩ := hq
    obtain ⟨hh,hy⟩ := hp
    have hb6 : b.val<6 := by simpa only [valid,decide_eq_true_eq] using hb
    split_ifs at hr with he
    rcases he with ⟨rfl,_⟩
    unfold event
    rw [fms_value R false ⟨g,hg⟩ ⟨y,hy⟩ b hb6,refinement_value R true ⟨g,hg⟩ ⟨k,hk⟩]
    exact bob_rejection R ⟨g,hg⟩ ⟨k,hk⟩ ⟨y,hy⟩ ⟨b.val,hb6⟩ a hr

def basic (q p : Question) (a b : ℕ) : Bool :=
  match q,p with
  | .binary n,.binary m => if n=m then decide (a=b) else true
  | .fms g x,.fms h y => if g=h then conditionalFmsRule x y a b else true
  | _,_ => true

theorem basic_zero {P : Presentation} (R : StructuralRealization P) (q p : Question)
    (hq : WellFormed P q) (hp : WellFormed P p) (a b : Fin 12)
    (ha : valid q a.val=true) (hb : valid p b.val=true)
    (hr : basic q p a.val b.val=false) : event R q p a b=0 := by
  cases q <;> cases p <;> simp only [basic,Bool.true_eq_false] at hr
  case binary.binary n m =>
    by_cases hn : n=m
    · subst m
      simp only [ite_true,decide_eq_false_iff_not] at hr
      have hab : a≠b := by intro h; exact hr (congrArg Fin.val h)
      exact CompilerHonestNamedCorrect.partition_rejection
        (CompilerHonestPregameBase.binary (CompilerOrientedProjections.projection R n) (CompilerOrientedProjections.projection_projective R n))
        (CompilerHonestPregameBase.binary (transpose (CompilerOrientedProjections.projection R n)) (transpose_projection _ (CompilerOrientedProjections.projection_projective R n))) _
        (CompilerHonestNamedCorrect.binary_mirrors _ _ (CompilerOrientedProjections.projection_projective R n) (CompilerOrientedProjections.projection_centralizer R n)) a b hab
    · simp only [if_neg hn,Bool.true_eq_false] at hr
  case fms.fms g x h y =>
    obtain ⟨hg,hx⟩ := hq
    obtain ⟨hh,hy⟩ := hp
    have ha6 : a.val<6 := by simpa only [valid,decide_eq_true_eq] using ha
    have hb6 : b.val<6 := by simpa only [valid,decide_eq_true_eq] using hb
    by_cases he : g=h
    · subst h
      rw [if_pos rfl] at hr
      unfold event
      rw [fms_value R false ⟨g,hg⟩ ⟨x,hx⟩ a ha6,fms_value R true ⟨g,hg⟩ ⟨y,hy⟩ b hb6]
      exact rejection R.density ⟨g,hg⟩ ⟨x,hx⟩ ⟨y,hy⟩ ⟨a.val,ha6⟩ ⟨b.val,hb6⟩ hr
    · simp only [if_neg he,Bool.true_eq_false] at hr

/-- All actual frozen pregame rejections annihilate the common state. -/
theorem rule_zero {P : Presentation} (R : StructuralRealization P) (q p : Question)
    (hq : WellFormed P q) (hp : WellFormed P p) (a b : Fin 12)
    (hr : rule P q p a.val b.val=false) : event R q p a b=0 := by
  by_cases ha : valid q a.val=false
  · unfold event
    rw [invalid_zero R false q a ha,CoarseCells.left_zero,zero_mul,zero_apply]
  by_cases hb : valid p b.val=false
  · unfold event
    rw [invalid_zero R true p b hb,CoarseCells.right_zero,mul_zero,zero_apply]
  have ha' : valid q a.val=true := Bool.eq_true_of_not_eq_false ha
  have hb' : valid p b.val=true := Bool.eq_true_of_not_eq_false hb
  simp only [rule,ha',hb',Bool.true_and,Bool.and_eq_false_iff] at hr
  rcases hr with (hr|hr)|hr
  · exact basic_zero R q p hq hp a b ha' hb' hr
  · exact directed_A_zero R q p hq hp a b ha' hb' hr
  · exact directed_B_zero R p q hp hq b a hb' ha' hr

theorem perfect {P : Presentation} (R : StructuralRealization P) :
    Perfect (preGame P) (strategy R) := by
  unfold Perfect loss
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  cases he : (preGame P).accepts x y a b
  · have hz := rule_zero R (question P x.val) (question P y.val)
      (question_wellFormed P x.val) (question_wellFormed P y.val) a b he
    simp only [Bool.false_eq_true,ite_false]
    suffices (strategy R).probability x y a b=0 by
      exact (congrArg (fun t : ℝ => ((preGame P).distribution x y:ℝ)*t) this).trans (mul_zero _)
    rw [CompilerHonestRefinementsCorrect.strategy,CompilerHonestPregameBase.strategy,
      CompilerHonestState.strategy,normalOfPure_probability]
    change (inner ℂ (vector (density R.density))
      (((CompilerHonestPregameBase.measurements R (refinements R false) (refinements R true)).left x a*
        (CompilerHonestPregameBase.measurements R (refinements R false) (refinements R true)).right y b)
          (vector (density R.density)))).re=0
    rw [measurements_left,measurements_right]
    change (inner ℂ (vector (density R.density)) (event R _ _ a b)).re=0
    rw [hz,inner_zero_right]
    rfl
  · simp only [ite_true,mul_zero]

#print axioms perfect
end Sigma2.CompilerHonestPregameCorrect
