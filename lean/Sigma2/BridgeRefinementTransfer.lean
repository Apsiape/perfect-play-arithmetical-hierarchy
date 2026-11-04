import Sigma2.RefinementModels
noncomputable section
open scoped BigOperators
namespace Sigma2.BridgeRefinementTransfer
open Compiler Preliminaries BridgeMatrixUnits RefinementModels

/-- The constructed matrix-unit part also holds for the original mixed strategy. -/
theorem normal_bridge_matrix_units {s} (S : NormalStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect S I) (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P) :
    let f := P*flagA S I*P
    let m := fun i => P*magicA S I i*P
    ∃ (e : Op) (t : Fin 4 → Fin 4 → Op),Projection e ∧ e=f+∑ i,m i ∧
      (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
      (∀ i j,star (t i j)=t j i) ∧ (∀ i,t i i=m i) ∧ (∀ i j,Centralizes h.op (t i j)) := by
  obtain ⟨T,hT,hA,hM,_⟩ := conditional_pure_model S I hS
  have hh := bridge_matrix_units T I hT h (hM h hm) P hP
  simpa only [flagA,magicA,normalOfPure,hA] using hh

/-- Exact original operator conclusion of Lemma 4.2. -/
def RefinementConclusion {s} (S : NormalStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (eA eB : Op) : Prop :=
    (∀ a,eA*(∑ z,S.measurements.alice F.newA (F.answerA a z))*eA=
        eA*S.measurements.alice (I.qA 3) (I.aA a)*eA) ∧
    (∀ b,eB*(∑ z,S.measurements.bob F.newB (F.answerB b z))*eB=
        eB*S.measurements.bob (I.qB 3) (I.aB b)*eB) ∧
    (∀ a,(eA*S.measurements.alice (I.qA 3) (I.aA a)*eA)*
        (eA*S.measurements.alice F.labelQA F.labelA*eA)=
      (eA*S.measurements.alice F.labelQA F.labelA*eA)*
        (eA*S.measurements.alice (I.qA 3) (I.aA a)*eA)) ∧
    (∀ b,(eB*S.measurements.bob (I.qB 3) (I.aB b)*eB)*
        (eB*S.measurements.bob F.labelQB F.labelB*eB)=
      (eB*S.measurements.bob F.labelQB F.labelB*eB)*
        (eB*S.measurements.bob (I.qB 3) (I.aB b)*eB))

/-- End-to-end transfer: pure Lemma 4.2 implies its unchanged mixed conclusion,
with both original marginal supports. The pure theorem is still an obligation. -/
theorem refinement_pure_transfer {s} (S : NormalStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect S I F)
    (hA hB : Density) (mA : MarginalA S hA) (mB : MarginalB S hB)
    (eA eB : Op) (sA : SupportOf hA eA) (sB : SupportOf hB eB)
    (hpure : ∀ (T : PureStrategy s),RefinementPerfect (normalOfPure T) I F →
      ∀ (kA kB : Density),MarginalA (normalOfPure T) kA → MarginalB (normalOfPure T) kB →
      ∀ (pA pB : Op),SupportOf kA pA → SupportOf kB pB →
      RefinementConclusion (normalOfPure T) I F pA pB) : RefinementConclusion S I F eA eB := by
  obtain ⟨T,hT,hAT,hMT,_⟩ := refinement_preserving_alice S I F hF
  obtain ⟨_,kB,_,mkB⟩ := marginals_exist (normalOfPure T)
  obtain ⟨pB,spB⟩ := support_exists kB
  obtain ⟨aEq,_,aComm,_⟩ := hpure T hT hA kB (hMT hA mA) mkB eA pB sA spB
  obtain ⟨U,hU,hBU,hMU,_⟩ := refinement_preserving_bob S I F hF
  obtain ⟨kA,_,mkA,_⟩ := marginals_exist (normalOfPure U)
  obtain ⟨pA,spA⟩ := support_exists kA
  obtain ⟨_,bEq,_,bComm⟩ := hpure U hU kA hB mkA (hMU hB mB) pA eB spA sB
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [normalOfPure,hAT] using aEq
  · simpa only [normalOfPure,hBU] using bEq
  · simpa only [normalOfPure,hAT] using aComm
  · simpa only [normalOfPure,hBU] using bComm

#print axioms normal_bridge_matrix_units
#print axioms refinement_pure_transfer
end Sigma2.BridgeRefinementTransfer
