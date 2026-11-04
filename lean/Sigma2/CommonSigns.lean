import Sigma2.BobCalibration

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CommonSigns
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness CalibrationCoordinates CalibrationSigns CalibrationReference ActualCalibration BobCalibration

theorem pulledB_supported {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (y : Fin 2) :
    pulledB S I Q y*colSupport (flagB S I Q) (bobUnit S I Q) 0=pulledB S I Q y := by
  have hg := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have hb : rowEmbed (flagB S I Q) (bobUnit S I Q) y*
      colSupport (flagB S I Q) (bobUnit S I Q) 0=rowEmbed (flagB S I Q) (bobUnit S I Q) y := by
    norm_num [rowEmbed,colSupport,up,phase,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      hg.flag.2,hg.flag_left,hg.flag_right,hg.mul,op_smul_zero]
  unfold pulledB
  rw [mul_assoc,hb]

theorem actual_common_signs {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    pulledA S I P 0=pulledA S I P 1 ∧ pulledB S I Q 0=pulledB S I Q 1 := by
  have h00 := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 0 0
  have h10 := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 1 0
  have h01 := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 0 1
  have ha : left (pulledA S I P 0) (referenceVector S I P)=left (pulledA S I P 1) (referenceVector S I P) := by
    have h0 : left (pulledA S I P 0) (referenceVector S I P)=right (pulledB S I Q 0) (referenceVector S I P) := by simpa [sigma,referenceVector] using h00
    have h1 : left (pulledA S I P 1) (referenceVector S I P)=right (pulledB S I Q 0) (referenceVector S I P) := by simpa [sigma,referenceVector] using h10
    exact h0.trans h1.symm
  have hb : right (pulledB S I Q 0) (referenceVector S I P)=right (pulledB S I Q 1) (referenceVector S I P) := by
    have h0 : left (pulledA S I P 0) (referenceVector S I P)=right (pulledB S I Q 0) (referenceVector S I P) := by simpa [sigma,referenceVector] using h00
    have h1 : left (pulledA S I P 0) (referenceVector S I P)=right (pulledB S I Q 1) (referenceVector S I P) := by simpa [sigma,referenceVector] using h01
    exact h0.symm.trans h1
  constructor
  · have hh := vector_cancel (referenceVector S I P) _ (pulledA S I P 0-pulledA S I P 1)
      (reference_range S I hS hA hmA P hP) (by rw [left_sub,sub_apply,ha,sub_self])
    rw [sub_mul,pulledA_supported S I hS hA hmA P hP 0,pulledA_supported S I hS hA hmA P hP 1] at hh
    exact sub_eq_zero.mp hh
  · have hz : left (pulledB S I Q 0-pulledB S I Q 1) (swap (referenceVector S I P))=0 := by
      have hh := congrArg swap hb
      rw [PureTransfer.swap_right,PureTransfer.swap_right] at hh
      rw [left_sub,sub_apply,hh,sub_self]
    have hh := vector_cancel (swap (referenceVector S I P)) _ (pulledB S I Q 0-pulledB S I Q 1)
      (bob_reference_range S I hS hA hB hmA hmB P Q hP hQ) hz
    rw [sub_mul,pulledB_supported S I hS hA hB hmA hmB P Q hP hQ 0,
      pulledB_supported S I hS hA hB hmA hmB P Q hP hQ 1] at hh
    exact sub_eq_zero.mp hh

#print axioms actual_common_signs
end Sigma2.CommonSigns
