import Sigma2.BridgeRefinementTransfer
import Sigma2.RefinementAlgebra
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RefinementCoarse
open Compiler Preliminaries TensorLifts PureSupport CoarseCells CalibrationEvents MirrorAlgebra

/-- A zero actual event annihilates the original pure vector. -/
theorem event_zero {s} (S : PureStrategy s) (x : QA s) (y : QB s) (a : AA s) (b : BB s)
    (hp : (normalOfPure S).probability x y a b=0) :
    (left (S.measurements.alice x a)*right (S.measurements.bob y b)) S.vector=0 := by
  rw [normalOfPure_probability] at hp
  change (inner ℂ S.vector ((S.measurements.left x a*S.measurements.right y b) S.vector)).re=0 at hp
  rw [measurements_left,measurements_right] at hp
  exact positive_apply_eq_zero _ (joint_positive _ _ (S.measurements.alice_pos x a)
    (S.measurements.bob_pos y b)) _ hp

/-- Two finite coarse measurements matched against the same unchanged question
have the same compressed effects on the original supplied state support. -/
theorem coarse_same {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (A E B : Fin 6 → Op) (hA : ∀ a,Positive (A a)) (hE : ∀ a,Positive (E a))
    (hB : ∀ b,Positive (B b)) (sA : ∑ a,A a=1) (sE : ∑ a,E a=1) (sB : ∑ b,B b=1)
    (hzA : ∀ a b,signClassA a≠signClassB 0 b → (left (A a)*right (B b)) S.vector=0)
    (hzE : ∀ a b,signClassA a≠signClassB 0 b → (left (E a)*right (B b)) S.vector=0) :
    ∀ t,P*coarse A signClassA t*P=P*coarse E signClassA t*P := by
  intro t
  have h1 := coarse_analysis S h hm P hP A B hA hB sA sB signClassA (signClassB 0)
    (fun a b hab => by rw [hzA a b hab]; simp) t
  have h2 := coarse_analysis S h hm P hP E B hE hB sE sB signClassA (signClassB 0)
    (fun a b hab => by rw [hzE a b hab]; simp) t
  have hv := h1.1.trans h2.1.symm
  apply local_eq S h hm P hP _ _
    (by simp only [mul_assoc,hP.1.2]) (by simp only [mul_assoc,hP.1.2])
  simp only [left_mul]
  change left P (left (coarse A signClassA t) (left P S.vector))=
    left P (left (coarse E signClassA t) (left P S.vector))
  rw [left_support S h hm P hP,hv]

def aliceNew {s} (S : PureStrategy s) {I : FMSInstance s} (F : LabelRefinementInstance s I)
    (a : Fin 6) : Op := ∑ z,S.measurements.alice F.newA (F.answerA a z)

def bobNew {s} (S : PureStrategy s) {I : FMSInstance s} (F : LabelRefinementInstance s I)
    (b : Fin 6) : Op := ∑ z,S.measurements.bob F.newB (F.answerB b z)

theorem alice_classes {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    ∀ t,P*coarse (aliceNew S F) signClassA t*P=
      P*coarse (fun a => S.measurements.alice (I.qA 3) (I.aA a)) signClassA t*P := by
  rcases hF with ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩
  apply coarse_same S h hm P hP (aliceNew S F)
    (fun a => S.measurements.alice (I.qA 3) (I.aA a))
    (fun b => S.measurements.bob (I.qB 0) (I.aB b))
  · intro a
    exact ContinuousLinearMap.isPositive_sum _ (fun z _ => S.measurements.alice_pos _ _)
  · intro a; exact S.measurements.alice_pos _ _
  · intro b; exact S.measurements.bob_pos _ _
  · exact sa
  · exact hc.2.1 3
  · exact hc.2.2 0
  · intro a b hab
    rw [aliceNew,left_sum,Finset.sum_mul,sum_apply]
    apply Finset.sum_eq_zero
    intro z _
    exact event_zero S _ _ _ _ (ha 0 (by simp) a z b (signClass_forbidden 0 a b hab))
  · intro a b hab
    exact event_zero S _ _ _ _ (hc.1 3 0 a b (signClass_forbidden 0 a b hab))

theorem bob_classes {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (h : Density) (hm : MarginalB (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    ∀ t,P*coarse (bobNew S F) signClassA t*P=
      P*coarse (fun b => S.measurements.bob (I.qB 3) (I.aB b)) signClassA t*P := by
  rcases hF with ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩
  have rule (a b : Fin 6) (hab : signClassA b≠signClassB 0 a) :
      conditionalFmsRule 0 3 a.val b.val=false := by
    fin_cases a <;> fin_cases b <;>
      norm_num [signClassA,signClassB,conditionalFmsRule,fmsRule,retained] at *
  apply coarse_same (PureTransfer.flipPure S) h hm P hP (bobNew S F)
    (fun b => S.measurements.bob (I.qB 3) (I.aB b))
    (fun a => S.measurements.alice (I.qA 0) (I.aA a))
  · intro b
    exact ContinuousLinearMap.isPositive_sum _ (fun z _ => S.measurements.bob_pos _ _)
  · intro b; exact S.measurements.bob_pos _ _
  · intro a; exact S.measurements.alice_pos _ _
  · exact sb
  · exact hc.2.2 3
  · exact hc.2.1 0
  · intro b a hab
    rw [bobNew,left_sum,Finset.sum_mul,sum_apply]
    apply Finset.sum_eq_zero
    intro z _
    apply event_zero (PureTransfer.flipPure S) F.newB (I.qA 0) (F.answerB b z) (I.aA a)
    have hh := hb 0 (by simp) a b z (rule a b hab)
    rw [normalOfPure_probability] at hh
    exact (normalOfPure_probability (PureTransfer.flipPure S) F.newB (I.qA 0) (F.answerB b z) (I.aA a)).trans
      ((PureTransfer.flipPure_probability S (I.qA 0) F.newB (I.aA a) (F.answerB b z)).trans hh)
  · intro b a hab
    apply event_zero (PureTransfer.flipPure S) (I.qB 3) (I.qA 0) (I.aB b) (I.aA a)
    have hh := hc.1 0 3 a b (rule a b hab)
    rw [normalOfPure_probability] at hh
    exact (normalOfPure_probability (PureTransfer.flipPure S) (I.qB 3) (I.qA 0) (I.aB b) (I.aA a)).trans
      ((PureTransfer.flipPure_probability S (I.qA 0) (I.qB 3) (I.aA a) (I.aB b)).trans hh)

/-- Exact retained, inactive, and total-sign recovery from the unchanged C0/R0
question, before the two individual signs are identified. -/
theorem class_recovery (A E : Fin 6 → Op) (P : Op)
    (hc : ∀ t,P*coarse A signClassA t*P=P*coarse E signClassA t*P) :
    P*(A 0+A 1)*P=P*(E 0+E 1)*P ∧
      ∀ a : Fin 6,2≤a.val → P*A a*P=P*E a*P := by
  constructor
  · simpa [coarse,signClassA,Fin.sum_univ_succ] using hc 0
  · intro a ha
    fin_cases a
    · norm_num at ha
    · norm_num at ha
    · simpa [coarse,signClassA,Fin.sum_univ_succ] using hc 1
    · simpa [coarse,signClassA,Fin.sum_univ_succ] using hc 2
    · simpa [coarse,signClassA,Fin.sum_univ_succ] using hc 3
    · simpa [coarse,signClassA,Fin.sum_univ_succ] using hc 5

#print axioms alice_classes
#print axioms bob_classes
#print axioms class_recovery
end Sigma2.RefinementCoarse
