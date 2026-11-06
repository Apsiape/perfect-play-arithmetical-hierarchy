import Sigma2.RefinementCoarse
import Sigma2.CalibrationSharpness
import Sigma2.BobCalibration
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RefinementSigns
open Compiler Preliminaries TensorLifts PureSupport CoarseCells FiniteSpectral MirrorAlgebra
  DiagonalIdentification CalibrationEvents CalibrationGeometry CalibrationDensity
  CalibrationSharpness FilteredSign RefinementCoarse

def small (a : Fin 2) : Fin 6 := ⟨a.val,by omega⟩

theorem filtered_zero (v : AB) (P Q R T A B : Op)
    (hvP : left P v=v) (hvQ : right Q v=v)
    (ha : (P*A*P)*R=P*A*P) (hb : (Q*B*Q)*T=Q*B*Q)
    (hz : (left A*right B) v=0) :
    (left (P*A*P)*right (Q*B*Q)) ((left R*right T) v)=0 := by
  change ((left (P*A*P)*right (Q*B*Q))*(left R*right T)) v=0
  rw [joint_mul,ha,hb,compressed_joint v P Q A B hvP hvQ,hz,map_zero]

theorem alice_signs {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (hA hB : Density) (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    ∀ a : Fin 6,P*aliceNew S F a*P=P*S.measurements.alice (I.qA 3) (I.aA a)*P := by
  have hc := hF.1
  let N : Fin 2 → Op := fun a => P*aliceNew S F (small a)*P
  let R := P*sumA S I 0*P
  let T := Q*sumB S I 0*Q
  let v := signVector S I P Q 0 0
  have hrec := class_recovery (aliceNew S F)
    (fun a => S.measurements.alice (I.qA 3) (I.aA a)) P (alice_classes S I F hF hA hmA P hP)
  have hsN : N 0+N 1=R := by
    simpa [N,R,small,sumA,signQuestion,mul_add,add_mul] using hrec.1
  have hpN (a : Fin 2) : Positive (N a) :=
    compressed_positive P hP.1 (fun a => aliceNew S F (small a))
      (fun a => ContinuousLinearMap.isPositive_sum _ (fun z _ => S.measurements.alice_pos _ _)) a
  have hns := binary_supported R (N 0) (N 1) (sign_sector S I hc hA hmA P hP 0).2.2.1
    (hpN 0) (hpN 1) hsN
  have heN (a : Fin 2) : N a*R=N a := by
    fin_cases a
    · exact hns.1.1
    · exact hns.2.1
  have he := effects_supported S I hc hA hB hmA hmB P Q hP hQ 0 0
  have hv := signVector_supported S I hc hA hB hmA hmB P Q hP hQ 0 0
  have raw (a b : Fin 2) (hab : a≠b) :
      (left (aliceNew S F (small a))*right (S.measurements.bob (I.qB 3) (I.aB (small b)))) S.vector=0 := by
    rw [aliceNew,left_sum,Finset.sum_mul,sum_apply]
    apply Finset.sum_eq_zero
    intro z _
    apply event_zero S F.newA (I.qB 3) (F.answerA (small a) z) (I.aB (small b))
    apply hF.2.2.2.1 3 (by simp) (small a) z (small b)
    fin_cases a <;> fin_cases b <;> norm_num [small,conditionalFmsRule,fmsRule] at *
  have hzN (a b : Fin 2) (hab : a≠b) :
      (left (N a)*right (effectB S I Q 0 b)) v=0 := by
    exact filtered_zero S.vector P Q R T (aliceNew S F (small a))
      (S.measurements.bob (I.qB 3) (I.aB (small b)))
      (left_support S hA hmA P hP) (right_support S hB hmB Q hQ) (heN a) (he.2 b) (raw a b hab)
  have hsame := RefinementAlgebra.binary_unique v R T
    (effectA S I P 0) N (effectB S I Q 0) hv.1 hv.2
    (effects_sumA S I P 0) hsN (effects_sumB S I Q 0) he.1 heN
    (fun a b hab => filtered_forbidden S I hc hA hB hmA hmB P Q hP hQ 0 0 a b (by
      fin_cases a <;> fin_cases b <;> norm_num at *)) hzN
    (fun A hz => vector_cancel v R A (signVector_range S I hc hA hB hmA hmB P Q hP hQ 0 0) hz)
  intro a
  fin_cases a
  · exact hsame 0
  · exact hsame 1
  · exact hrec.2 2 (by decide)
  · exact hrec.2 3 (by decide)
  · exact hrec.2 4 (by decide)
  · exact hrec.2 5 (by decide)

theorem bob_signs {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (hA hB : Density) (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    ∀ b : Fin 6,Q*bobNew S F b*Q=Q*S.measurements.bob (I.qB 3) (I.aB b)*Q := by
  have hc := hF.1
  let N : Fin 2 → Op := fun b => Q*bobNew S F (small b)*Q
  let R := P*sumA S I 0*P
  let T := Q*sumB S I 0*Q
  let v := signVector S I P Q 0 0
  have hrec := class_recovery (bobNew S F)
    (fun b => S.measurements.bob (I.qB 3) (I.aB b)) Q (bob_classes S I F hF hB hmB Q hQ)
  have hsN : N 0+N 1=T := by
    simpa [N,T,small,sumB,signQuestion,mul_add,add_mul] using hrec.1
  have hpN (b : Fin 2) : Positive (N b) :=
    compressed_positive Q hQ.1 (fun b => bobNew S F (small b))
      (fun b => ContinuousLinearMap.isPositive_sum _ (fun z _ => S.measurements.bob_pos _ _)) b
  have hns := binary_supported T (N 0) (N 1) (bob_sign_sector S I hc hB hmB Q hQ 0).2.2
    (hpN 0) (hpN 1) hsN
  have heN (b : Fin 2) : N b*T=N b := by
    fin_cases b
    · exact hns.1.1
    · exact hns.2.1
  have he := effects_supported S I hc hA hB hmA hmB P Q hP hQ 0 0
  have hv := signVector_supported S I hc hA hB hmA hmB P Q hP hQ 0 0
  have raw (a b : Fin 2) (hab : a≠b) :
      (left (S.measurements.alice (I.qA 3) (I.aA (small a)))*right (bobNew S F (small b))) S.vector=0 := by
    rw [bobNew,right_sum,Finset.mul_sum,sum_apply]
    apply Finset.sum_eq_zero
    intro z _
    apply event_zero S (I.qA 3) F.newB (I.aA (small a)) (F.answerB (small b) z)
    apply hF.2.2.2.2.1 3 (by simp) (small a) (small b) z
    fin_cases a <;> fin_cases b <;> norm_num [small,conditionalFmsRule,fmsRule] at *
  have hzN (b a : Fin 2) (hab : b≠a) :
      (left (N b)*right (effectA S I P 0 a)) (TensorLifts.swap v)=0 := by
    have hz := filtered_zero S.vector P Q R T
      (S.measurements.alice (I.qA 3) (I.aA (small a))) (bobNew S F (small b))
      (left_support S hA hmA P hP) (right_support S hB hmB Q hQ) (he.1 a) (heN b) (raw a b hab.symm)
    have hh := congrArg TensorLifts.swap hz
    rw [PureTransfer.swap_joint,map_zero] at hh
    exact hh
  have hvT : left T (TensorLifts.swap v)=TensorLifts.swap v := by
    have hh := congrArg TensorLifts.swap hv.2
    rwa [PureTransfer.swap_right] at hh
  have hvR : right R (TensorLifts.swap v)=TensorLifts.swap v := by
    have hh := congrArg TensorLifts.swap hv.1
    rwa [PureTransfer.swap_left] at hh
  have hsame := RefinementAlgebra.binary_unique (TensorLifts.swap v) T R
    (effectB S I Q 0) N (effectA S I P 0) hvT hvR
    (effects_sumB S I Q 0) hsN (effects_sumA S I P 0) he.2 heN
    (fun b a hab => by
      have hz := filtered_forbidden S I hc hA hB hmA hmB P Q hP hQ 0 0 a b (by
        fin_cases a <;> fin_cases b <;> norm_num at *)
      have hh := congrArg TensorLifts.swap hz
      rwa [PureTransfer.swap_joint,map_zero] at hh) hzN
    (fun A hz => by
      have hh := congrArg TensorLifts.swap hz
      rw [PureTransfer.swap_left,TensorLifts.swap_swap,map_zero] at hh
      exact BobCalibration.bob_sign_cancel S I hc hA hB hmA hmB P Q hP hQ 0 A hh)
  intro b
  fin_cases b
  · exact hsame 0
  · exact hsame 1
  · exact hrec.2 2 (by decide)
  · exact hrec.2 3 (by decide)
  · exact hrec.2 4 (by decide)
  · exact hrec.2 5 (by decide)

#print axioms alice_signs
#print axioms bob_signs
end Sigma2.RefinementSigns


