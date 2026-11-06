import Sigma2.BridgeVector
import Sigma2.ExtractionBlocks

set_option synthInstance.maxHeartbeats 10000
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.RawBridgeVector
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness CalibrationCoordinates CalibrationSigns CalibrationReference ActualCalibration
  BobCalibration BridgeVector ExtractionBlocks

theorem pure_vector {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) :
    (S.measurements.left (I.qA 4) (I.aA 2)*S.measurements.right (I.qB 0) (I.aB 1)) S.vector=
      (Real.sqrt 2:ℂ) • ((left (transportA (normalOfPure S) I)*right (transportB (normalOfPure S) I))
        ((S.measurements.left (I.qA 0) (I.aA 0)*S.measurements.right (I.qB 0) (I.aB 0)) S.vector)) := by
  obtain ⟨hA,hB,hmA,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨P,hP⟩ := support_exists hA
  obtain ⟨Q,hQ⟩ := support_exists hB
  have hu := units_analysis S I hS hA hmA P hP
  have hf := actual_frame S I hS hA hmA P hP
  have hg := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have hp := (flag_pair S I hS hA hB hmA hmB P Q hP hQ).1
  have hm := (units_mirror S I hS hA hB hmA hmB P Q hP hQ 0 0).1
  have hPs := left_support S hA hmA P hP
  have hQs := right_support S hB hmB Q hQ
  have hfAc : Commute P (flagA (normalOfPure S) I) := (SharpEvents.conditional_flag_sharp S I hS hA hmA P hP).1.symm
  have hmAc : Commute P (magicA (normalOfPure S) I 0) := (SharpEvents.conditional_magic_sharp S I hS hA hmA P hP 0).1.symm
  have hfBc : Commute Q (S.measurements.bob (I.qB 0) (I.aB 0)) :=
    (bob_reduce S Q hQ.1 _ _ (flagB_projection S I hS hB hmB Q hQ)).symm
  have hnproj : Projection (Q*S.measurements.bob (I.qB 0) (I.aB 1)*Q) := by
    rw [← bob_zero_diagonal S I hS hA hB hmA hmB P Q hP hQ]
    exact ⟨hg.adjoint 0 0,by simpa only [ite_true] using hg.mul 0 0 0 0⟩
  have hmBc : Commute Q (S.measurements.bob (I.qB 0) (I.aB 1)) := (bob_reduce S Q hQ.1 _ _ hnproj).symm
  have hflag : (left (flagA (normalOfPure S) I)*right (S.measurements.bob (I.qB 0) (I.aB 0))) S.vector=
      left (P*flagA (normalOfPure S) I*P) S.vector := by
    rw [← compressed_joint_action S.vector P Q _ _ hP.1 hQ.1 hPs hQs hfAc hfBc]
    change left (P*flagA (normalOfPure S) I*P) (right (flagB S I Q) S.vector)=_
    rw [← hp]
    change left ((P*flagA (normalOfPure S) I*P)*(P*flagA (normalOfPure S) I*P)) S.vector=_
    rw [hf.flag.2]
  have hmagic : (left (magicA (normalOfPure S) I 0)*right (S.measurements.bob (I.qB 0) (I.aB 1))) S.vector=
      left (actualUnit S I P 0 0) S.vector := by
    rw [← compressed_joint_action S.vector P Q _ _ hP.1 hQ.1 hPs hQs hmAc hmBc,
      ← hu.2.2.1 0,← bob_zero_diagonal S I hS hA hB hmA hmB P Q hP hQ]
    change left (actualUnit S I P 0 0) (right (bobUnit S I Q 0 0) S.vector)=_
    rw [← hm]
    change left (actualUnit S I P 0 0*actualUnit S I P 0 0) S.vector=_
    rw [hf.mul,if_pos rfl]
  have hh := actual_component S I hS hA hB hmA hmB P Q hP hQ
  have hw : actualUnit S I P 0 0*differenceA S I P 0*(P*flagA (normalOfPure S) I*P)=
      P*transportA (normalOfPure S) I*P := by
    rw [hu.2.2.1,differenceA_eq]
    exact compressed_transport P _ _ _ hP.1
      (SharpEvents.conditional_magic_sharp S I hS hA hmA P hP 0).1
      (SharpEvents.conditional_flag_sharp S I hS hA hmA P hP).1
  dsimp only at hh
  rw [hw,bob_extraction S I hS hA hB hmA hmB P Q hP hQ] at hh
  have hpFlag : left P (left (P*flagA (normalOfPure S) I*P) S.vector)=
      left (P*flagA (normalOfPure S) I*P) S.vector := by
    change left (P*(P*flagA (normalOfPure S) I*P)) S.vector=_
    simp only [← mul_assoc,hP.1.2]
  have hqFlag : right Q (left (P*flagA (normalOfPure S) I*P) S.vector)=
      left (P*flagA (normalOfPure S) I*P) S.vector := by rw [← commute_on,hQs]
  have hr := transports_reduce S I hS hA hB hmA hmB P Q hP hQ
  rw [compressed_joint_action _ P Q _ _ hP.1 hQ.1 hpFlag hqFlag hr.1 hr.2] at hh
  rw [measurements_left,measurements_right,measurements_left,measurements_right]
  change (left (magicA (normalOfPure S) I 0)*right (S.measurements.bob (I.qB 0) (I.aB 1))) S.vector=_
  change (left (S.measurements.alice (I.qA 0) (I.aA 0))*right (S.measurements.bob (I.qB 0) (I.aB 0))) S.vector=_ at hflag
  rw [hmagic,hflag]
  exact hh

theorem conditional_component {s} (S : NormalStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect S I) (k : ℕ) (hk : 0<S.weight k) :
    ConditionalPerfect (normalOfPure (S.component k)) I := by
  refine ⟨?_,hS.2.1,hS.2.2⟩
  intro x y a b hr
  rw [normalOfPure_probability]
  have hp := (event_summable S (I.qA x) (I.qB y) (I.aA a) (I.aB b)).le_tsum k
    (fun j _ => mul_nonneg (S.weight_nonneg j) (pure_probability_nonnegative _ _ _ _ _))
  change S.weight k*(S.component k).probability (I.qA x) (I.qB y) (I.aA a) (I.aB b)≤
    S.probability (I.qA x) (I.qB y) (I.aA a) (I.aB b) at hp
  rw [hS.1 x y a b hr] at hp
  have hz : S.weight k*(S.component k).probability (I.qA x) (I.qB y) (I.aA a) (I.aB b)=0 :=
    le_antisymm hp (mul_nonneg (S.weight_nonneg k) (pure_probability_nonnegative _ _ _ _ _))
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hk)

/-- The untouched original positive-weight component quantifier of Eq. (12). -/
theorem mixed_vector {s} (S : NormalStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect S I) : CalibratedIdentity S I := by
  intro k hk
  exact pure_vector (S.component k) I (conditional_component S I hS k hk)

#print axioms pure_vector
#print axioms mixed_vector
end Sigma2.RawBridgeVector
