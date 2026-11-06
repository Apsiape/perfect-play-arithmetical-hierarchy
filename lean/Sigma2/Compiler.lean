import Sigma2.CompilerBase
import Sigma2.RowBooleanClosure
import Sigma2.ActualCalibration
import Sigma2.RawBridgeVector
import Sigma2.ActualRefinement

noncomputable section
open scoped BigOperators
namespace Sigma2.Compiler

/-- Lemma 4.1, normal bridge. The partial isometry is the calibrated actual
sign block, rather than an independently chosen unitary gauge. -/
theorem lemma_4_1_normal_bridge {s} (S : NormalStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect S I) (h : Density) (hm : MarginalA S h)
    (support : Op) (hsupport : Preliminaries.SupportOf h support) :
    let f := support*flagA S I*support
    let m := fun i => support*magicA S I i*support
    let w := support*transportA S I*support
    ∃ (e : Op) (t : Fin 4 → Fin 4 → Op),
      Projection e ∧ e=f+∑ i,m i ∧
      (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
      (∀ i j,star (t i j)=t j i) ∧ (∀ i,t i i=m i) ∧
      (∀ i j,Centralizes h.op (t i j)) ∧
      star w*w=f ∧ w*star w=m 0 ∧ h.op*w=(2:ℂ) • (w*h.op) := by
  exact Sigma2.ActualCalibration.actual_normal_bridge S I hS h hm support hsupport


/-- Eq. (12), calibrated component identity, including Bob's sqrt(2) extraction.
The assertion is on every positive-weight component of the original mixed state,
so it also holds on its untouched environment purification. -/
theorem calibrated_bridge_vector {s} (S : NormalStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect S I) :
    ∃ A B : BipOp,
      (∀ v i j,(A v) (i,j)=∑' k,entry (transportA S I) i k*v (k,j)) ∧
      (∀ v i j,(B v) (i,j)=∑' k,entry (transportB S I) j k*v (i,k)) ∧
      ∀ k,0<S.weight k →
        (S.measurements.left (I.qA 4) (I.aA 2)*S.measurements.right (I.qB 0) (I.aB 1)) (S.vector k)=
          (Real.sqrt 2:ℂ) • ((A*B)
            ((S.measurements.left (I.qA 0) (I.aA 0)*
              S.measurements.right (I.qB 0) (I.aB 0)) (S.vector k))) := by
  exact (Sigma2.calibrated_vector_iff S I).mpr (Sigma2.RawBridgeVector.mixed_vector S I hS)


/-- Lemma 4.2 at the actual unchanged-question predicate interface. The original
signs, retained answers and inactive answer are recovered on each state support;
each label is refined separately, without label-label commutation. The converse
product construction is `joint_refinement_iff` above. -/
theorem lemma_4_2_label_refinement {s} (S : NormalStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect S I F)
    (hA hB : Density) (mA : MarginalA S hA) (mB : MarginalB S hB)
    (eA eB : Op) (sA : Preliminaries.SupportOf hA eA) (sB : Preliminaries.SupportOf hB eB) :
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
        (eB*S.measurements.bob (I.qB 3) (I.aB b)*eB)) := by
  exact ActualRefinement.actual_refinement S I F hF hA hB mA mB eA eB sA sB


/-- Lemma 4.3, Boolean rational rows, soundness and simultaneous extension.
The finite maximally entangled ancilla is incorporated in T's state. -/
theorem lemma_4_3_boolean_rows (G : Game) (R : Rows G.scenario) :
    ∃ (G' : Game) (E : ScenarioEmbedding G.scenario G'.scenario),
      (∀ T, Perfect G' T → ∃ S, Perfect G S ∧ Extends E S T ∧ RowsHold R S) ∧
      (∀ S, Perfect G S → RowsHold R S → NamedBinaryProjections R S →
        ∃ T, Perfect G' T ∧ Extends E S T ∧
          (FiniteMarginalEntropy S → FiniteMarginalEntropy T)) := by
  exact RowCompleteness.boolean_rows G R

end Sigma2.Compiler
