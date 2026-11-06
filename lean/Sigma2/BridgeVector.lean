import Sigma2.BobCalibration

set_option synthInstance.maxHeartbeats 10000
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.BridgeVector
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness CalibrationCoordinates CalibrationSigns CalibrationReference ActualCalibration BobCalibration

theorem sqrtTwo_invSqrtTwo : (Real.sqrt 2:ℂ)*invSqrtTwo=1 := by
  have hh : (Real.sqrt 2:ℂ)*(Real.sqrt 2:ℂ)=2 := by exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)
  unfold invSqrtTwo
  calc
    _=((Real.sqrt 2:ℂ)*(Real.sqrt 2:ℂ))/2 := by ring
    _=1 := by rw [hh]; norm_num

/-- The component calculation in the written proof. Bob's forward block is
read from the actual mirrored sign; no independent unitary is substituted. -/
theorem component_from_mirror (omegaF omegaM : AB) (f m g n X Y w : Op)
    (hff : left f omegaF=omegaF) (hfm : left f omegaM=0)
    (hnf : right n omegaF=0) (hnm : right n omegaM=omegaM)
    (hmm : left m omegaM=omegaM) (hgg : right g omegaF=omegaF)
    (hstar : star w=f*X*m) (hwm : w*star w=m)
    (hm : left X (omegaF+invSqrtTwo • omegaM)=right Y (omegaF+invSqrtTwo • omegaM)) :
    omegaM=(Real.sqrt 2:ℂ) • ((left w*right (n*Y*g)) omegaF) := by
  let v := omegaF+invSqrtTwo • omegaM
  have hnv : right n v=invSqrtTwo • omegaM := by simp only [v,map_add,map_smul,hnf,hnm,zero_add]
  have hfv : left f v=omegaF := by simp only [v,map_add,map_smul,hff,hfm,smul_zero,add_zero]
  have hs : left (f*X) omegaM=left (star w) omegaM := by
    rw [hstar]
    change left (f*X) omegaM=left (f*X) (left m omegaM)
    rw [hmm]
  have hL : left f (right n (left X v))=invSqrtTwo • left (star w) omegaM := by
    rw [← commute_on X n v,hnv,map_smul,map_smul]
    change invSqrtTwo • left (f*X) omegaM=_
    rw [hs]
  have hR : left f (right n (right Y v))=right (n*Y*g) omegaF := by
    change left f (right (n*Y) v)=_
    rw [commute_on,hfv]
    change right (n*Y) omegaF=right (n*Y) (right g omegaF)
    rw [hgg]
  have hh := congrArg (fun z : AB => left f (right n z)) hm
  change left f (right n (left X v))=left f (right n (right Y v)) at hh
  rw [hL,hR] at hh
  have hblock := congrArg (left w) hh
  rw [map_smul] at hblock
  change invSqrtTwo • left (w*star w) omegaM=(left w*right (n*Y*g)) omegaF at hblock
  rw [hwm,hmm] at hblock
  calc
    omegaM=(Real.sqrt 2:ℂ) • (invSqrtTwo • omegaM) := by rw [smul_smul,sqrtTwo_invSqrtTwo,one_smul]
    _=_ := by rw [hblock]

theorem actual_component {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    let f := P*flagA (normalOfPure S) I*P
    let m := actualUnit S I P 0 0
    let g := flagB S I Q
    let n := bobUnit S I Q 0 0
    let w := m*differenceA S I P 0*f
    left m S.vector=(Real.sqrt 2:ℂ) •
      ((left w*right (n*pulledB S I Q 0*g)) (left f S.vector)) := by
  let f := P*flagA (normalOfPure S) I*P
  let m := actualUnit S I P 0 0
  let g := flagB S I Q
  let n := bobUnit S I Q 0 0
  have hf := actual_frame S I hS hA hmA P hP
  have hg := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have hp := (flag_pair S I hS hA hB hmA hmB P Q hP hQ).1
  have hm := (units_mirror S I hS hA hB hmA hmB P Q hP hQ 0 0).1
  have hx := (alice_sign_properties S I hS hA hB hmA hmB P Q hP hQ 0).1
  have hu := units_analysis S I hS hA hmA P hP
  have hw : m*differenceA S I P 0*f=P*transportA (normalOfPure S) I*P := by
    change actualUnit S I P 0 0*differenceA S I P 0*(P*flagA (normalOfPure S) I*P)=_
    rw [hu.2.2.1,differenceA_eq]
    exact compressed_transport P _ _ _ hP.1
      (SharpEvents.conditional_magic_sharp S I hS hA hmA P hP 0).1
      (SharpEvents.conditional_flag_sharp S I hS hA hmA P hP).1
  have hwm := (pure_calibration S I hS hA hmA P hP).2.1
  rw [← hw,← hu.2.2.1 0] at hwm
  have hstar : star (m*differenceA S I P 0*f)=f*differenceA S I P 0*m := by
    have hfs : star f=f := hf.flag.1
    have hms : star m=m := hf.adjoint 0 0
    rw [star_mul (m*differenceA S I P 0) f,star_mul m (differenceA S I P 0),hfs,hms,hx]
    noncomm_ring
  have hmatch := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 0 0
  rw [pulledA_zero S I hS hA hB hmA hmB P Q hP hQ] at hmatch
  have he : left (differenceA S I P 0) (left f S.vector+invSqrtTwo • left m S.vector)=
      right (pulledB S I Q 0) (left f S.vector+invSqrtTwo • left m S.vector) := by
    simpa [f,m,sigma,left_add,left_smul,add_apply,smul_apply] using hmatch
  apply component_from_mirror _ _ f m g n _ _ _ _ _ _ _ _ _ hstar hwm he
  · change left (f*f) S.vector=left f S.vector
    rw [hf.flag.2]
  · change left (f*m) S.vector=0
    rw [hf.flag_left,left_zero,zero_apply]
  · rw [← commute_on,← hm]
    change left (f*m) S.vector=0
    rw [hf.flag_left,left_zero,zero_apply]
  · rw [← commute_on,← hm]
    change left (m*m) S.vector=left m S.vector
    rw [hf.mul,if_pos rfl]
  · change left (m*m) S.vector=left m S.vector
    rw [hf.mul,if_pos rfl]
  · rw [← commute_on,← hp]
    change left (f*f) S.vector=left f S.vector
    rw [hf.flag.2]

#print axioms component_from_mirror
#print axioms actual_component
end Sigma2.BridgeVector
