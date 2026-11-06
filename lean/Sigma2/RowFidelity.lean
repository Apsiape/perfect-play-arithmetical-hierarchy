import Sigma2.RowSynchronization
import Sigma2.RowInterface
import Sigma2.RefinementLabel
import Sigma2.RefinementModels

set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowFidelity
open Compiler Preliminaries TensorLifts PureSupport PureTransfer RowSynchronization

/-- The retained half-effect diagnostic fails the corrected premise by the
actual old probability of a disagreeing answer pair. -/
theorem coin_not_synchronized :
    ¬ BinaryEventSynchronized RowInterface.coin (RowInterface.halfRow.event ⟨0,by decide⟩) := by
  intro hs
  have hz := hs 0 1 (by decide)
  rw [RowInterface.coin_probability] at hz
  norm_num at hz

theorem coin_not_named_binary :
    ¬ NamedBinaryProjections RowInterface.halfRow RowInterface.coin := by
  intro hs
  exact coin_not_synchronized ((named_iff_synchronized _ _).mp hs ⟨0,by decide⟩)

/-- A sharp supported event and its actual opposite mirror have zero binary
disagreement. No projectivity of the other old answers is used. -/
theorem pure_synchronized_of_mirror {s} (S : PureStrategy s) (e : NamedEvent s)
    (h : Density) (hm : MarginalA (normalOfPure S) h)
    (P : Op) (hP : SupportOf h P)
    (hsharp : BinaryProjectionOn P (S.measurements.alice e.x e.a))
    (hmirror : S.measurements.left e.x e.a S.vector=
      S.measurements.right e.y e.b S.vector) :
    BinaryEventSynchronized (normalOfPure S) e := by
  let E := S.measurements.left e.x e.a
  let F := S.measurements.right e.y e.b
  have hEP : S.measurements.alice e.x e.a*P=
      P*S.measurements.alice e.x e.a*P := by
    calc
      _ = S.measurements.alice e.x e.a*(P*P) := by rw [hP.1.2]
      _ = (S.measurements.alice e.x e.a*P)*P := by noncomm_ring
      _ = _ := by rw [hsharp.1]
  have hlocal : S.measurements.alice e.x e.a*S.measurements.alice e.x e.a*P=
      S.measurements.alice e.x e.a*P := by
    calc
      _ = (S.measurements.alice e.x e.a*P)*(S.measurements.alice e.x e.a*P) := by
        symm
        calc
          _ = S.measurements.alice e.x e.a*(P*S.measurements.alice e.x e.a)*P := by noncomm_ring
          _ = S.measurements.alice e.x e.a*(S.measurements.alice e.x e.a*P)*P := by rw [← hsharp.1]
          _ = (S.measurements.alice e.x e.a*S.measurements.alice e.x e.a)*(P*P) := by noncomm_ring
          _ = _ := by rw [hP.1.2]
      _ = _ := by rw [hEP,hsharp.2.2]
  have hid : E (E S.vector)=E S.vector := by
    have hp := MirrorAlgebra.left_support S h hm P hP
    have heq : E*E*left P=E*left P := by
      dsimp only [E]
      rw [measurements_left]
      simpa only [left_mul] using congrArg left hlocal
    have hh := congrArg (fun L : BipOp => L S.vector) heq
    simpa only [mul_apply_eq_comp,hp] using hh
  have hzR : (E*(1-F)) S.vector=0 := by
    change E (S.vector-F S.vector)=0
    rw [map_sub,← hmirror,hid,sub_self]
  have hzL : ((1-E)*F) S.vector=0 := by
    change F S.vector-E (F S.vector)=0
    rw [← hmirror,hid,sub_self]
  have restR : 1-F=∑ b ∈ Finset.univ.erase e.b,S.measurements.right e.y b := by
    have hh := Finset.sum_erase_add Finset.univ (S.measurements.right e.y)
      (Finset.mem_univ e.b)
    rw [S.measurements.right_sum] at hh
    exact (eq_sub_iff_add_eq.mpr hh).symm
  have restL : 1-E=∑ a ∈ Finset.univ.erase e.a,S.measurements.left e.x a := by
    have hh := Finset.sum_erase_add Finset.univ (S.measurements.left e.x)
      (Finset.mem_univ e.a)
    rw [S.measurements.left_sum] at hh
    exact (eq_sub_iff_add_eq.mpr hh).symm
  have sumR : (∑ b ∈ Finset.univ.erase e.b,S.probability e.x e.y e.a b)=0 := by
    have hh := congrArg (fun v : AB => (inner ℂ S.vector v).re) hzR
    rw [restR,Finset.mul_sum,sum_apply,inner_sum,complex_re_sum] at hh
    simpa only [E,PureStrategy.probability,inner_zero_right,Complex.zero_re] using hh
  have sumL : (∑ a ∈ Finset.univ.erase e.a,S.probability e.x e.y a e.b)=0 := by
    have hh := congrArg (fun v : AB => (inner ℂ S.vector v).re) hzL
    rw [restL,Finset.sum_mul,sum_apply,inner_sum,complex_re_sum] at hh
    simpa only [F,PureStrategy.probability,inner_zero_right,Complex.zero_re] using hh
  intro a b hab
  rw [normalOfPure_probability]
  by_cases ha : a=e.a
  · subst a
    have hb : b≠e.b := by simpa using hab
    apply le_antisymm _ (pure_probability_nonnegative _ _ _ _ _)
    calc
      _ ≤ ∑ b ∈ Finset.univ.erase e.b,S.probability e.x e.y e.a b :=
        Finset.single_le_sum (fun b _ => pure_probability_nonnegative _ _ _ _ _)
          (Finset.mem_erase.mpr ⟨hb,Finset.mem_univ b⟩)
      _ = 0 := sumR
  · have hb : b=e.b := by tauto
    subst b
    apply le_antisymm _ (pure_probability_nonnegative _ _ _ _ _)
    calc
      _ ≤ ∑ a ∈ Finset.univ.erase e.a,S.probability e.x e.y a e.b :=
        Finset.single_le_sum (fun a _ => pure_probability_nonnegative _ _ _ _ _)
          (Finset.mem_erase.mpr ⟨ha,Finset.mem_univ a⟩)
      _ = 0 := sumL

/-- This converse preserves the original mixed state through the checked
operator- and marginal-preserving purification. -/
theorem synchronized_of_mirror {s} (S : NormalStrategy s) (e : NamedEvent s)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (hsharp : BinaryProjectionOn P (S.measurements.alice e.x e.a))
    (hmirror : ∀ k,0<S.weight k → S.measurements.left e.x e.a (S.vector k)=
      S.measurements.right e.y e.b (S.vector k)) :
    BinaryEventSynchronized S e := by
  obtain ⟨T,hA,_,hM,hprob,hmir⟩ := RefinementPureTransfer.preserving_alice_with_mirrors S
  have hs : BinaryProjectionOn P (T.measurements.alice e.x e.a) := by
    simpa only [hA] using hsharp
  have hh := pure_synchronized_of_mirror T e h (hM h hm) P hP hs
    (hmir e.x e.y e.a e.b hmirror)
  intro a b hab
  rw [hprob,← normalOfPure_probability]
  exact hh a b hab

/-- Expose the sharp-label conclusion already proved in the stage 7 refinement
argument, at the original label effect rather than a replacement event. -/
theorem pure_refinement_label_sharp {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    Projection (P*S.measurements.alice F.labelQA F.labelA*P) := by
  rcases hF with ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩
  apply (RefinementLabel.label_matching S h hm P hP
    (fun a z => S.measurements.alice F.newA (F.answerA a z))
    (S.measurements.bob F.labelQB)
    (fun a z => S.measurements.alice_pos _ _) (S.measurements.bob_pos F.labelQB)
    sa (S.measurements.bob_sum F.labelQB) F.labelB
    (S.measurements.alice F.labelQA F.labelA) ?_ ?_).2.1
  · intro a z b hr
    exact RefinementCoarse.event_zero S _ _ _ _ (hza a z b hr)
  · have hh := hlabel 0 (by norm_num [normalOfPure])
    rw [measurements_left,measurements_right] at hh
    exact hh

/-- The existing pure refinement predicate supplies synchronization of its
original named label, via its already proved sharpness and mirror. -/
theorem pure_refinement_label_synchronized {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    BinaryEventSynchronized (normalOfPure S) ⟨F.labelQA,F.labelQB,F.labelA,F.labelB⟩ := by
  have hmirror : S.measurements.left F.labelQA F.labelA S.vector=
      S.measurements.right F.labelQB F.labelB S.vector :=
    hF.2.2.2.2.2.2.2 0 (by norm_num [normalOfPure])
  have hmirror' : left (S.measurements.alice F.labelQA F.labelA) S.vector=
      right (S.measurements.bob F.labelQB F.labelB) S.vector := by
    simpa only [measurements_left,measurements_right] using hmirror
  have hc := matching_commutes_support S h hm P hP
    (S.measurements.alice F.labelQA F.labelA) (S.measurements.bob F.labelQB F.labelB)
    (S.measurements.alice_pos F.labelQA F.labelA) hmirror'
  exact pure_synchronized_of_mirror S ⟨F.labelQA,F.labelQB,F.labelA,F.labelB⟩ h hm P hP
    ⟨hc,pure_refinement_label_sharp S I F hF h hm P hP⟩ hmirror

/-- Each actual refinement label supplies binary synchronization from its
existing predicate, with no new input assumption. Correlations are unchanged. -/
theorem refinement_label_synchronized {s} (S : NormalStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect S I F) :
    BinaryEventSynchronized S ⟨F.labelQA,F.labelQB,F.labelA,F.labelB⟩ := by
  obtain ⟨T,hT,hA,hM,hprob⟩ := RefinementModels.refinement_preserving_alice S I F hF
  obtain ⟨h,hB,hm,hmB⟩ := marginals_exist (normalOfPure T)
  obtain ⟨P,hP⟩ := support_exists h
  have hh := pure_refinement_label_synchronized T I F hT h hm P hP
  intro a b hab
  exact (hprob _ _ a b).trans ((normalOfPure_probability T _ _ a b).symm.trans (hh a b hab))

/-- Every finite family of existing refinement labels supplies exactly the new
Lemma 4.3 premise, on the same strategy and actual named questions/answers. -/
theorem refinement_family_named {s} (S : NormalStrategy s) (R : Rows s)
    (I : Fin R.count → FMSInstance s) (F : ∀ i,LabelRefinementInstance s (I i))
    (hF : ∀ i,RefinementPerfect S (I i) (F i))
    (hname : ∀ i,R.event i=⟨(F i).labelQA,(F i).labelQB,(F i).labelA,(F i).labelB⟩) :
    NamedBinaryProjections R S := by
  apply named_of_synchronized
  intro i
  rw [hname]
  exact refinement_label_synchronized S (I i) (F i) (hF i)

#print axioms coin_not_synchronized
#print axioms coin_not_named_binary
#print axioms pure_synchronized_of_mirror
#print axioms synchronized_of_mirror
#print axioms pure_refinement_label_sharp
#print axioms pure_refinement_label_synchronized
#print axioms refinement_label_synchronized
#print axioms refinement_family_named
end Sigma2.RowFidelity
