import Sigma2.CompilerBase
import Sigma2.PureTransfer
import Sigma2.VectorTransfer
import Sigma2.PureSupport
noncomputable section
open scoped BigOperators
namespace Sigma2
open Compiler PureTransfer

theorem conditional_pure_model {s} (S : NormalStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect S I) :
    ∃ T : PureStrategy s,
      ConditionalPerfect (normalOfPure T) I ∧
      T.measurements.alice=S.measurements.alice ∧
      (∀ h : Density,MarginalA S h → MarginalA (normalOfPure T) h) ∧
      (∀ x y a b,S.probability x y a b=T.probability x y a b) := by
  obtain ⟨T,hA,hB,hm,hp⟩ := preserving_alice S
  refine ⟨T,?_,hA,hm,hp⟩
  refine ⟨?_,?_,?_⟩
  · intro x y a b hr
    rw [normalOfPure_probability,← hp]
    exact hS.1 x y a b hr
  · intro x
    change (∑ a,T.measurements.alice (I.qA x) (I.aA a))=1
    rw [hA]
    exact hS.2.1 x
  · intro y
    change (∑ b,T.measurements.bob (I.qB y) (I.aB b))=1
    rw [hB,← Purification.amplify_sum,hS.2.2 y,Purification.amplify_one]

/-- The exact unchanged target of Lemma 4.1, with no bridge facts in its fields. -/
def BridgeConclusion {s} (S : NormalStrategy s) (I : FMSInstance s)
    (h : Density) (support : Op) : Prop :=
    let f := support*flagA S I*support
    let m := fun i => support*magicA S I i*support
    let w := support*transportA S I*support
    ∃ (e : Op) (t : Fin 4 → Fin 4 → Op),
      Projection e ∧ e=f+∑ i,m i ∧
      (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
      (∀ i j,star (t i j)=t j i) ∧ (∀ i,t i i=m i) ∧
      (∀ i j,Centralizes h.op (t i j)) ∧
      star w*w=f ∧ w*star w=m 0 ∧ h.op*w=(2:ℂ) • (w*h.op)

/-- Only the pure-state bridge remains to establish the original mixed theorem.
This is a proved reduction of obligations, not an assumed pure bridge. -/
theorem bridge_pure_transfer {s} (S : NormalStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect S I) (h : Density) (hm : MarginalA S h)
    (support : Op) (hsupport : Preliminaries.SupportOf h support)
    (hpure : ∀ T : PureStrategy s,ConditionalPerfect (normalOfPure T) I →
      MarginalA (normalOfPure T) h → Preliminaries.SupportOf h support →
      BridgeConclusion (normalOfPure T) I h support) : BridgeConclusion S I h support := by
  obtain ⟨T,hT,hA,hM,_⟩ := conditional_pure_model S I hS
  have hh := hpure T hT (hM h hm) hsupport
  simpa only [BridgeConclusion,flagA,magicA,transportA,normalOfPure,hA] using hh


/-- The remaining Eq. (6) obligation, after the completed-space lifts are fixed. -/
def CalibratedIdentity {s} (S : NormalStrategy s) (I : FMSInstance s) : Prop :=
  ∀ k,0<S.weight k →
    (S.measurements.left (I.qA 4) (I.aA 2)*S.measurements.right (I.qB 0) (I.aB 1)) (S.vector k)=
      (Real.sqrt 2:ℂ) • ((TensorLifts.left (transportA S I)*TensorLifts.right (transportB S I))
        ((S.measurements.left (I.qA 0) (I.aA 0)*
          S.measurements.right (I.qB 0) (I.aB 0)) (S.vector k)))

/-- The original calibrated-vector target is equivalent to its sole remaining
vector equation. Bounded lift construction and uniqueness are fully proved. -/
theorem calibrated_vector_iff {s} (S : NormalStrategy s) (I : FMSInstance s) :
    (∃ A B : BipOp,
      (∀ v i j,(A v) (i,j)=∑' k,entry (transportA S I) i k*v (k,j)) ∧
      (∀ v i j,(B v) (i,j)=∑' k,entry (transportB S I) j k*v (i,k)) ∧
      ∀ k,0<S.weight k →
        (S.measurements.left (I.qA 4) (I.aA 2)*S.measurements.right (I.qB 0) (I.aB 1)) (S.vector k)=
          (Real.sqrt 2:ℂ) • ((A*B)
            ((S.measurements.left (I.qA 0) (I.aA 0)*
              S.measurements.right (I.qB 0) (I.aB 0)) (S.vector k)))) ↔ CalibratedIdentity S I := by
  constructor
  · rintro ⟨A,B,hA,hB,hv⟩
    have hAl : A=TensorLifts.left (transportA S I) := by
      ext v ⟨i,j⟩
      rw [hA,TensorLifts.left_coordinates]
    have hBr : B=TensorLifts.right (transportB S I) := by
      ext v ⟨i,j⟩
      rw [hB,TensorLifts.right_coordinates]
    simpa only [hAl,hBr,CalibratedIdentity] using hv
  · intro hv
    exact ⟨TensorLifts.left (transportA S I),TensorLifts.right (transportB S I),
      TensorLifts.left_coordinates _,TensorLifts.right_coordinates _,hv⟩

#print axioms conditional_pure_model
#print axioms bridge_pure_transfer
#print axioms calibrated_vector_iff
end Sigma2
