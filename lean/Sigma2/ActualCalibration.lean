import Sigma2.CalibrationReference
import Sigma2.CalibrationTransport
import Sigma2.BridgeTransfer

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.ActualCalibration
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness CalibrationCoordinates CalibrationSigns CalibrationReference CalibrationTransport

theorem bob_difference_selfadjoint {s} (S : PureStrategy s) (I : FMSInstance s)
    (Q : Op) (hQ : Projection Q) (y : Fin 2) : star (differenceB S I Q y)=differenceB S I Q y := by
  have hp (b : Fin 2) : Positive (effectB S I Q y b) :=
    compressed_positive Q hQ
      (fun b : Fin 6 => S.measurements.bob (I.qB (signQuestion y)) (I.aB b))
      (fun b => S.measurements.bob_pos _ _) ⟨b.val,by omega⟩
  exact (star_sub (effectB S I Q y 0) (effectB S I Q y 1)).trans
    (congrArg₂ (fun A B : Op => A-B) (hp 0).isSelfAdjoint.star_eq (hp 1).isSelfAdjoint.star_eq)

theorem pulledB_selfadjoint {s} (S : PureStrategy s) (I : FMSInstance s)
    (Q : Op) (hQ : Projection Q) (y : Fin 2) : star (pulledB S I Q y)=pulledB S I Q y := by
  unfold pulledB
  rw [star_mul,star_mul,star_star,bob_difference_selfadjoint S I Q hQ y]
  noncomm_ring

theorem actual_modular_commutator {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    let K := (P*flagA (normalOfPure S) I*P+(1/2:ℂ) • actualUnit S I P 0 0)*hA.op
    differenceA S I P 0*K=K*differenceA S I P 0 := by
  have he := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 0 0
  rw [pulledA_zero S I hS hA hB hmA hmB P Q hP hQ] at he
  have hm : left (differenceA S I P 0) (referenceVector S I P)=
      right (pulledB S I Q 0) (referenceVector S I P) := by
    simpa [referenceVector,sigma] using he
  have hh := mirrors_covariance (referenceVector S I P) (differenceA S I P 0) (pulledB S I Q 0)
    (alice_sign_properties S I hS hA hB hmA hmB P Q hP hQ 0).1
    (pulledB_selfadjoint S I Q hQ.1 0) hm
  have hc := (coefficient_covariance (referenceVector S I P)).symm.trans
    (reference_covariance S I hS hA hmA P hP)
  rw [hc] at hh
  exact hh

theorem compressed_transport (P M D F : Op) (hP : Projection P)
    (hM : M*P=P*M) (hF : F*P=P*F) :
    (P*M*P)*(P*D*P)*(P*F*P)=P*(M*D*F)*P := by
  have hMP : P*M*P=P*M := by rw [← hM,mul_assoc,hP.2,hM]
  have hFP : P*F*P=F*P := by rw [← hF,mul_assoc,hP.2]
  calc
    _=(P*M)*(P*P)*D*(P*P)*F*P := by noncomm_ring
    _=(P*M*P)*D*(P*F*P) := by rw [hP.2]; noncomm_ring
    _=(P*M)*D*(F*P) := by rw [hMP,hFP]
    _=_ := by noncomm_ring

/-- All three calibration equations for the actual original transport block. -/
theorem pure_calibration {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    let f := P*flagA (normalOfPure S) I*P
    let m := P*magicA (normalOfPure S) I 0*P
    let w := P*transportA (normalOfPure S) I*P
    star w*w=f ∧ w*star w=m ∧ h.op*w=(2:ℂ) • (w*h.op) := by
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  have hf := actual_frame S I hS h hm P hP
  have hu := units_analysis S I hS h hm P hP
  have hx := alice_sign_properties S I hS h hB hm hmB P Q hP hQ 0
  have hs := (actual_sign_supports S I hS h hB hm hmB P Q hP hQ 0 0).1
  rw [hs] at hx
  have hm0 : Projection (actualUnit S I P 0 0) := ⟨hf.adjoint 0 0,by simpa only [ite_true] using hf.mul 0 0 0 0⟩
  have hh := transport_from_sign h.op (P*flagA (normalOfPure S) I*P) (actualUnit S I P 0 0)
    (differenceA S I P 0) hf.flag hm0 (hf.flag_left 0 0) (hf.flag_right 0 0)
    hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
    (actual_anticommutation S I hS h hB hm hmB P Q hP hQ)
    (flag_centralizes S I hS h hm P hP).eq (hu.2.2.2.1 0 0)
    (actual_modular_commutator S I hS h hB hm hmB P Q hP hQ)
  have hw : actualUnit S I P 0 0*differenceA S I P 0*(P*flagA (normalOfPure S) I*P)=
      P*transportA (normalOfPure S) I*P := by
    rw [hu.2.2.1,differenceA_eq]
    have he := compressed_transport P (magicA (normalOfPure S) I 0) (signA S I 0)
      (flagA (normalOfPure S) I) hP.1
      (SharpEvents.conditional_magic_sharp S I hS h hm P hP 0).1
      (SharpEvents.conditional_flag_sharp S I hS h hm P hP).1
    exact he
  dsimp only at hh ⊢
  rw [hw,hu.2.2.1] at hh
  exact hh

theorem pure_normal_bridge {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    BridgeConclusion (normalOfPure S) I h P := by
  obtain ⟨e,t,he,hs,hprod,hstar,hdiag,hcentral⟩ := bridge_matrix_units S I hS h hm P hP
  obtain ⟨hwf,hwm,hwmod⟩ := pure_calibration S I hS h hm P hP
  exact ⟨e,t,he,hs,hprod,hstar,hdiag,hcentral,hwf,hwm,hwmod⟩

theorem actual_normal_bridge {s} (S : NormalStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect S I) (h : Density) (hm : MarginalA S h)
    (P : Op) (hP : SupportOf h P) : BridgeConclusion S I h P :=
  bridge_pure_transfer S I hS h hm P hP (fun T hT hmT hPT => pure_normal_bridge T I hT h hmT P hPT)

#print axioms pure_calibration
#print axioms actual_normal_bridge
end Sigma2.ActualCalibration
