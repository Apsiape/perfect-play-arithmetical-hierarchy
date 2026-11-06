import Sigma2.RefinementPureTransfer
noncomputable section
open scoped BigOperators
namespace Sigma2.RefinementModels
open Compiler Purification PureTransfer RefinementPureTransfer

theorem refinement_of_events {s} (S : NormalStrategy s) (T : PureStrategy s)
    (I : FMSInstance s) (F : LabelRefinementInstance s I) (hF : RefinementPerfect S I F)
    (hp : ∀ x y a b,S.probability x y a b=T.probability x y a b)
    (hA : ∀ x,∑ a,T.measurements.alice (I.qA x) (I.aA a)=1)
    (hB : ∀ y,∑ b,T.measurements.bob (I.qB y) (I.aB b)=1)
    (hnA : (∑ a,∑ z,T.measurements.alice F.newA (F.answerA a z))=1)
    (hnB : (∑ b,∑ z,T.measurements.bob F.newB (F.answerB b z))=1)
    (hmirror : T.measurements.left F.labelQA F.labelA T.vector=
      T.measurements.right F.labelQB F.labelB T.vector) : RefinementPerfect (normalOfPure T) I F := by
  rcases hF with ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩
  have hz (x y a b) (hh : S.probability x y a b=0) :
      (normalOfPure T).probability x y a b=0 := by rw [normalOfPure_probability,← hp]; exact hh
  refine ⟨⟨?_,hA,hB⟩,hnA,hnB,?_,?_,?_,?_,?_⟩
  · intro x y a b hr
    exact hz _ _ _ _ (hc.1 x y a b hr)
  · intro y hy a z b hr
    exact hz _ _ _ _ (ha y hy a z b hr)
  · intro x hx a b z hr
    exact hz _ _ _ _ (hb x hx a b z hr)
  · intro a z b hr
    exact hz _ _ _ _ (hza a z b hr)
  · intro a b z hr
    exact hz _ _ _ _ (hzb a b z hr)
  · intro k hk
    exact hmirror

theorem refinement_preserving_alice {s} (S : NormalStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect S I F) :
    ∃ T : PureStrategy s,RefinementPerfect (normalOfPure T) I F ∧
      T.measurements.alice=S.measurements.alice ∧
      (∀ h : Density,MarginalA S h → MarginalA (normalOfPure T) h) ∧
      (∀ x y a b,S.probability x y a b=T.probability x y a b) := by
  obtain ⟨T,hA,hB,hm,hp,hmir⟩ := preserving_alice_with_mirrors S
  rcases hF with ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩
  refine ⟨T,?_,hA,hm,hp⟩
  apply refinement_of_events S T I F ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩ hp
  · intro x
    rw [hA]
    exact hc.2.1 x
  · intro y
    rw [hB,← amplify_sum,hc.2.2 y,amplify_one]
  · rw [hA]
    exact sa
  · rw [hB]
    simp_rw [← amplify_sum]
    rw [sb,amplify_one]
  · exact hmir F.labelQA F.labelQB F.labelA F.labelB hlabel

theorem refinement_preserving_bob {s} (S : NormalStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect S I F) :
    ∃ T : PureStrategy s,RefinementPerfect (normalOfPure T) I F ∧
      T.measurements.bob=S.measurements.bob ∧
      (∀ h : Density,MarginalB S h → MarginalB (normalOfPure T) h) ∧
      (∀ x y a b,S.probability x y a b=T.probability x y a b) := by
  obtain ⟨T,hM,hm,hp,hmir⟩ := preserving_bob_with_mirrors S
  have hA : T.measurements.alice=(fun x a => amplify (S.measurements.alice x a)) := by rw [hM]; rfl
  have hB : T.measurements.bob=S.measurements.bob := by rw [hM]; rfl
  rcases hF with ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩
  refine ⟨T,?_,hB,hm,hp⟩
  apply refinement_of_events S T I F ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩ hp
  · intro x
    rw [hA,← amplify_sum,hc.2.1 x,amplify_one]
  · intro y
    rw [hB]
    exact hc.2.2 y
  · rw [hA]
    simp_rw [← amplify_sum]
    rw [sa,amplify_one]
  · rw [hB]
    exact sb
  · exact hmir F.labelQA F.labelQB F.labelA F.labelB hlabel

#print axioms refinement_preserving_alice
#print axioms refinement_preserving_bob
end Sigma2.RefinementModels
