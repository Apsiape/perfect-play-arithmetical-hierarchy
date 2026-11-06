import Sigma2.RowParity
import Sigma2.FiniteJoint

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame TensorLifts Preliminaries CoarseCells FiniteSpectral MirrorAlgebra

abbrev Answer (G : Game) (R : Rows G.scenario) := AA (scenario G R)

def newEffects (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (q : NewQ R) : Answer G R → Op :=
  compressed P (if bob then M.bob (qb G R q) else M.alice (qa G R q))

def LocalMarginal (bob : Bool) {s} (S : NormalStrategy s) (h : Density) : Prop :=
  if bob then MarginalB S h else MarginalA S h

theorem newRule_comm {s} (R : Rows s) (q p : Q R) (a b : ℕ) :
    newRule R q p a b=newRule R p q b a := by
  unfold newRule
  by_cases he : q=p
  · subst p; simp [eq_comm,Bool.and_comm,Bool.and_left_comm,Bool.and_assoc]
  · simp [he,Ne.symm he,Bool.and_comm,Bool.and_left_comm,Bool.and_assoc]

private theorem pure_coarse_identify {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x z : QA s) (y : QB s) (f u : ℕ → Bool)
    (hxy : ∀ a b,f a.val≠u b.val → S.probability x y a b=0)
    (hzy : ∀ a b,u a.val≠u b.val → S.probability z y a b=0) (t : Bool) :
    coarse (compressed P (S.measurements.alice x)) (fun a => f a.val) t=
      coarse (compressed P (S.measurements.alice z)) (fun a => u a.val) t ∧
    Projection (coarse (compressed P (S.measurements.alice x)) (fun a => f a.val) t) := by
  have han (w : QA s) (v : ℕ → Bool)
      (hz : ∀ a b,v a.val≠u b.val → S.probability w y a b=0) :=
    coarse_analysis S h hm P hP
      (S.measurements.alice w) (S.measurements.bob y)
      (S.measurements.alice_pos _) (S.measurements.bob_pos _)
      (S.measurements.alice_sum _) (S.measurements.bob_sum _)
      (fun a => v a.val) (fun b => u b.val)
      (fun a b hab => by simpa only [PureStrategy.probability,measurements_left,measurements_right] using hz a b hab) t
  have hx := han x f hxy
  have hz := han z u hzy
  refine ⟨?_,by rw [coarse_compressed]; exact hx.2.2.1⟩
  rw [coarse_compressed,coarse_compressed]
  apply local_eq S h hm P hP _ _ (by simp [mul_assoc,hP.1.2]) (by simp [mul_assoc,hP.1.2])
  have hs := left_support S h hm P hP
  have h1 := compressed_mirror S.vector P 1 _ _ hs (by simp [right_one]) hx.1
  have h2 := compressed_mirror S.vector P 1 _ _ hs (by simp [right_one]) hz.1
  exact h1.trans h2.symm

/-- Every Boolean binding is an equality of actual local sharp coarse effects,
on either original supplied marginal support. -/
theorem new_coarse_eq (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (q p : NewQ R) (f u : ℕ → Bool)
    (hz : ∀ a b,f a≠u b → newRule R q.val p.val a b=false) (t : Bool) :
    coarse (newEffects bob G R S.measurements P q) (fun a => f a.val) t=
      coarse (newEffects bob G R S.measurements P p) (fun a => u a.val) t ∧
    Projection (coarse (newEffects bob G R S.measurements P q) (fun a => f a.val) t) := by
  have hdiag (a b : ℕ) (hab : u a≠u b) : newRule R p.val p.val a b=false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have heq : a=b := by
      simp only [newRule,Bool.and_eq_true,ite_true,decide_eq_true_eq] at he
      exact he.1.1.2
    exact hab (congrArg u heq)
  cases bob
  · obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
    have hp (x z : NewQ R) (a b : Answer G R) (hab : newRule R x.val z.val a.val b.val=false) :
        T.probability (qa G R x) (qb G R z) a b=0 := by
      rw [← hprob]
      apply rejected_probability G R S hS
      change accepts G R _ _ _ _=false
      simpa only [accepts,decode_qa,decode_qb] using hab
    have hh := pure_coarse_identify T h (hM h hm) P hP (qa G R q) (qa G R p) (qb G R p) f u
      (fun a b hab => hp q p a b (hz a.val b.val hab))
      (fun a b hab => hp p p a b (hdiag a.val b.val hab)) t
    simpa [newEffects,Bool.false_eq_true,ite_false,hA] using hh
  · obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
    let W := PureTransfer.flipPure T
    have hp (x z : NewQ R) (a b : Answer G R) (hab : newRule R x.val z.val a.val b.val=false) :
        W.probability (qb G R x) (qa G R z) a b=0 := by
      rw [PureTransfer.flipPure_probability,← hprob]
      apply rejected_probability G R S hS
      change accepts G R _ _ _ _=false
      simp only [accepts,decode_qa,decode_qb]
      rw [newRule_comm]
      exact hab
    have hh := pure_coarse_identify W h (hM h hm) P hP (qb G R q) (qb G R p) (qa G R p) f u
      (fun a b hab => hp q p a b (hz a.val b.val hab))
      (fun a b hab => hp p p a b (hdiag a.val b.val hab)) t
    simpa [newEffects,Bool.true_eq,ite_true,W,PureTransfer.flipPure,
      PureTransfer.flipMeasurements,Purification.measurements,TensorLifts.measurements,hB,Answer,AA,BB,scenario,PureTransfer.flipScenario] using hh

private theorem pure_zero {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x : QA s) (y : QB s) (a : AA s) (hz : ∀ b,S.probability x y a b=0) :
    compressed P (S.measurements.alice x) a=0 := by
  have hs : (∑ b,S.probability x y a b)=
      (inner ℂ S.vector (left (S.measurements.alice x a) S.vector)).re := by
    simp only [PureStrategy.probability,← complex_re_sum,← inner_sum,
      ← sum_apply,← Finset.mul_sum,S.measurements.right_sum,mul_one,measurements_left]
  have he : (inner ℂ S.vector (left (S.measurements.alice x a) S.vector)).re=0 := by
    rw [← hs]; simp only [hz,Finset.sum_const_zero]
  have hh := PureSupport.zero_on_support S h hm P hP _ (S.measurements.alice_pos x a) he
  simp only [compressed,mul_assoc,hh.1,mul_zero]

theorem new_invalid_zero (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (q : NewQ R) (a : Answer G R) (ha : valid R q.val a.val=false) :
    newEffects bob G R S.measurements P q a=0 := by
  cases bob
  · obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
    have hh := pure_zero T h (hM h hm) P hP (qa G R q) (qb G R q) a (fun b => by
      rw [← hprob]; apply rejected_probability G R S hS
      change accepts G R _ _ _ _=false
      simp only [accepts,decode_qa,decode_qb,newRule,ha,Bool.false_and])
    simpa [newEffects,Bool.false_eq_true,ite_false,hA] using hh
  · obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
    have hh := pure_zero (PureTransfer.flipPure T) h (hM h hm) P hP (qb G R q) (qa G R q) a (fun b => by
      rw [PureTransfer.flipPure_probability,← hprob]; apply rejected_probability G R S hS
      change accepts G R _ _ _ _=false
      simp [accepts,decode_qa,decode_qb,newRule,ha])
    simpa [newEffects,Bool.true_eq,ite_true,PureTransfer.flipPure,
      PureTransfer.flipMeasurements,Purification.measurements,TensorLifts.measurements,hB,Answer,AA,BB,scenario,PureTransfer.flipScenario] using hh

theorem new_positive (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (hP : Projection P) (q : NewQ R) :
    ∀ a,Positive (newEffects bob G R M P q a) := by
  cases bob
  · exact compressed_positive P hP _ (M.alice_pos _)
  · exact compressed_positive P hP _ (M.bob_pos _)

theorem new_sum (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (hP : Projection P) (q : NewQ R) :
    ∑ a,newEffects bob G R M P q a=P := by
  cases bob
  · exact compressed_sum P hP _ (M.alice_sum _)
  · exact compressed_sum P hP _ (M.bob_sum _)

#print axioms newRule_comm
#print axioms pure_coarse_identify
#print axioms new_coarse_eq
#print axioms pure_zero
#print axioms new_invalid_zero
#print axioms new_positive
#print axioms new_sum
end Sigma2.RowScalar





