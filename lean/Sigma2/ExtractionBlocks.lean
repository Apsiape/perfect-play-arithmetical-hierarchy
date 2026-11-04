import Sigma2.BobCalibration

set_option synthInstance.maxHeartbeats 10000
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.ExtractionBlocks
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness CalibrationCoordinates CalibrationSigns CalibrationReference ActualCalibration BobCalibration

theorem bob_zero_diagonal {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    bobUnit S I Q 0 0=Q*S.measurements.bob (I.qB 0) (I.aB 1)*Q :=
  bob_diagonal S I hS hA hB hmA hmB P Q hP hQ 0

theorem bob_reduce {s} (S : PureStrategy s) (Q : Op) (hQ : Projection Q)
    (y : QB s) (b : BB s) (hp : Projection (Q*S.measurements.bob y b*Q)) :
    S.measurements.bob y b*Q=Q*S.measurements.bob y b := by
  apply sharp_compression Q _ hQ _ hp
  refine ⟨S.measurements.bob_pos y b,?_⟩
  have hh := positive_sum_erase (S.measurements.bob y) (S.measurements.bob_pos y) b
  rwa [S.measurements.bob_sum] at hh

theorem alice_reduce {s} (S : PureStrategy s) (P : Op) (hP : Projection P)
    (x : QA s) (a : AA s) (hp : Projection (P*S.measurements.alice x a*P)) :
    S.measurements.alice x a*P=P*S.measurements.alice x a := by
  apply sharp_compression P _ hP _ hp
  refine ⟨S.measurements.alice_pos x a,?_⟩
  have hh := positive_sum_erase (S.measurements.alice x) (S.measurements.alice_pos x) a
  rwa [S.measurements.alice_sum] at hh

/-- The actual retained (+++) answer of Bob's B1 question is matched to
Alice's R0 (+++) answer, before compressions are used. -/
theorem retained_bob {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hB : Density)
    (hmB : MarginalB (normalOfPure S) hB) (Q : Op) (hQ : SupportOf hB Q) :
    right (S.measurements.bob (I.qB 4) (I.aB 2)) S.vector=
      left (S.measurements.alice (I.qA 0) (I.aA 1)) S.vector ∧
    S.measurements.bob (I.qB 4) (I.aB 2)*Q=Q*S.measurements.bob (I.qB 4) (I.aB 2) ∧
    Projection (Q*S.measurements.bob (I.qB 4) (I.aB 2)*Q) := by
  have hz (a b : Fin 6) (hr : conditionalFmsRule 0 4 a.val b.val=false) :
      (inner ℂ (swap S.vector) ((left (S.measurements.bob (I.qB 4) (I.aB b))*
        right (S.measurements.alice (I.qA 0) (I.aA a))) (swap S.vector))).re=0 := by
    have he := (PureTransfer.flipPure_probability S (I.qA 0) (I.qB 4) (I.aA a) (I.aB b)).trans
      ((normalOfPure_probability S _ _ _ _).symm.trans (hS.1 0 4 a b hr))
    exact he
  have hAB (a : Fin 6) (ha : a≠1) := hz a 2 (by
    fin_cases a <;> norm_num [conditionalFmsRule,fmsRule,retained] at *)
  have hBA (b : Fin 6) (hb : b≠2) := hz 1 b (by
    fin_cases b <;> norm_num [conditionalFmsRule,fmsRule,retained] at *)
  have hh := SharpEvents.single_matching_analysis (PureTransfer.flipPure S) hB hmB Q hQ
    (fun b => S.measurements.bob (I.qB 4) (I.aB b))
    (fun a => S.measurements.alice (I.qA 0) (I.aA a))
    (fun b => S.measurements.bob_pos _ _) (fun a => S.measurements.alice_pos _ _)
    (hS.2.2 4) (hS.2.1 0) 2 1 hAB hBA
  have he := congrArg swap hh.1
  refine ⟨?_,hh.2.1,hh.2.2⟩
  simpa only [PureTransfer.flipPure,PureTransfer.swap_left,PureTransfer.swap_right,swap_swap] using he

theorem retained_bob_identification {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    Q*S.measurements.bob (I.qB 4) (I.aB 2)*Q=
      rowSupport (flagB S I Q) (bobUnit S I Q) 0-flagB S I Q := by
  have hp := flag_pair S I hS hA hB hmA hmB P Q hP hQ
  have hm := units_mirror S I hS hA hB hmA hmB P Q hP hQ
  have hh := row_support_mirror S.vector _ _ _ _ hp.1 (fun i j => (hm i j).1) 0
  have hdir : left (rowDirection S I P 0) S.vector=
      right (rowSupport (flagB S I Q) (bobUnit S I Q) 0-flagB S I Q) S.vector := by
    have he : rowSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) 0-
        (P*flagA (normalOfPure S) I*P)=rowDirection S I P 0 := by
      rw [actual_row_direction S I hS hA hmA P hP 0]
      unfold rowSupport
      abel
    rw [← he,left_sub,right_sub,sub_apply,sub_apply,hh,hp.1]
  have hr := compressed_mirror S.vector P Q _ _ (left_support S hA hmA P hP)
    (right_support S hB hmB Q hQ) (retained_bob S I hS hB hmB Q hQ).1.symm
  apply right_local_eq S hB hmB Q hQ _ _ (by simp only [mul_assoc,hQ.1.2]) _ (hr.symm.trans hdir)
  rw [sub_mul,← bob_sign_support S I hS hA hB hmA hmB P Q hP hQ 0]
  simp only [flagB,mul_assoc,hQ.1.2]

theorem compressed_word (P M R D F : Op) (hP : Projection P)
    (hM : M*P=P*M) (hR : R*P=P*R) (hF : F*P=P*F) :
    (P*M*P)*(P*R*P)*(P*D*P)*(P*F*P)=P*(M*R*D*F)*P := by
  have hMR : (M*R)*P=P*(M*R) := by
    calc
      _=M*(R*P) := by noncomm_ring
      _=M*(P*R) := by rw [hR]
      _=(M*P)*R := by noncomm_ring
      _=(P*M)*R := by rw [hM]
      _=_ := by noncomm_ring
  have hMP : P*M*P=P*M := by rw [← hM,mul_assoc,hP.2,hM]
  have hprod : (P*M*P)*(P*R*P)=P*(M*R)*P := by
    calc
      _=(P*M*P)*R*P := by
        calc
          _=P*M*(P*P)*R*P := by noncomm_ring
          _=_ := by rw [hP.2]
      _=_ := by rw [hMP]; noncomm_ring
  rw [hprod]
  exact compressed_transport P (M*R) D F hP hMR hF

/-- Bob's reference-coordinate forward block is exactly the prescribed
sqrt(2)-normalized compressed extraction. -/
theorem bob_extraction {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    bobUnit S I Q 0 0*pulledB S I Q 0*flagB S I Q=Q*transportB (normalOfPure S) I*Q := by
  let g := flagB S I Q
  let u := bobUnit S I Q
  let b := rowEmbed g u 0
  have hg : Frame g u := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have hbg : b*g=g := by
    norm_num [b,rowEmbed,phase,add_mul,mul_add,smul_mul_assoc,hg.flag.2,hg.flag_right,op_smul_zero]
  have hn : u 0 0*star b=(Real.sqrt 2:ℂ) • (u 0 0*(rowSupport g u 0-g)) := by
    norm_num [b,rowEmbed,rowSupport,phase,op_star_add,op_star_smul,hg.flag.1,hg.adjoint,
      invSqrtTwo_star,mul_add,mul_sub,mul_smul_comm,hg.flag_left,hg.flag_right,hg.mul,
      invSqrtTwo,op_smul_zero]
    module
  have hbeta : u 0 0*pulledB S I Q 0*g=(Real.sqrt 2:ℂ) •
      (u 0 0*(rowSupport g u 0-g)*differenceB S I Q 0*g) := by
    change u 0 0*(star b*differenceB S I Q 0*b)*g=_
    calc
      _=(u 0 0*star b)*differenceB S I Q 0*(b*g) := by noncomm_ring
      _=_ := by rw [hn,hbg]; simp only [smul_mul_assoc]
  rw [hbeta]
  dsimp only [u,g]
  rw [← retained_bob_identification S I hS hA hB hmA hmB P Q hP hQ,
    bob_zero_diagonal S I hS hA hB hmA hmB P Q hP hQ,differenceB_eq]
  change (Real.sqrt 2:ℂ) •
    ((Q*S.measurements.bob (I.qB 0) (I.aB 1)*Q)*(Q*S.measurements.bob (I.qB 4) (I.aB 2)*Q)*
      (Q*signB S I 0*Q)*(Q*S.measurements.bob (I.qB 0) (I.aB 0)*Q))=_
  have hnproj : Projection (Q*S.measurements.bob (I.qB 0) (I.aB 1)*Q) := by
    rw [← bob_zero_diagonal S I hS hA hB hmA hmB P Q hP hQ]
    exact ⟨hg.adjoint 0 0,by simpa only [ite_true] using hg.mul 0 0 0 0⟩
  rw [compressed_word Q _ _ _ _ hQ.1 (bob_reduce S Q hQ.1 _ _ hnproj)
    (retained_bob S I hS hB hmB Q hQ).2.1
    (bob_reduce S Q hQ.1 _ _ (flagB_projection S I hS hB hmB Q hQ))]
  simp only [transportB,mul_smul_comm,smul_mul_assoc]
  rfl

theorem signA_reduces {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x : Fin 2) :
    Commute P (signA S I x) := by
  have h0 := alice_reduce S P hP.1 _ _ (alice_sign_sharp S I hS hA hB hmA hmB P Q hP hQ x 0)
  have h1 := alice_reduce S P hP.1 _ _ (alice_sign_sharp S I hS hA hB hmA hmB P Q hP hQ x 1)
  change S.measurements.alice (I.qA (signQuestion x)) (I.aA 0)*P=P*S.measurements.alice (I.qA (signQuestion x)) (I.aA 0) at h0
  change S.measurements.alice (I.qA (signQuestion x)) (I.aA 1)*P=P*S.measurements.alice (I.qA (signQuestion x)) (I.aA 1) at h1
  change P*(S.measurements.alice _ _-S.measurements.alice _ _)=
    (S.measurements.alice _ _-S.measurements.alice _ _)*P
  rw [mul_sub,sub_mul,← h0,← h1]

theorem signB_reduces {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (y : Fin 2) :
    Commute Q (signB S I y) := by
  have h0 := bob_reduce S Q hQ.1 _ _ (bob_sign_sharp S I hS hA hB hmA hmB P Q hP hQ y 0)
  have h1 := bob_reduce S Q hQ.1 _ _ (bob_sign_sharp S I hS hA hB hmA hmB P Q hP hQ y 1)
  change S.measurements.bob (I.qB (signQuestion y)) (I.aB 0)*Q=Q*S.measurements.bob (I.qB (signQuestion y)) (I.aB 0) at h0
  change S.measurements.bob (I.qB (signQuestion y)) (I.aB 1)*Q=Q*S.measurements.bob (I.qB (signQuestion y)) (I.aB 1) at h1
  change Q*(S.measurements.bob _ _-S.measurements.bob _ _)=
    (S.measurements.bob _ _-S.measurements.bob _ _)*Q
  rw [mul_sub,sub_mul,← h0,← h1]

theorem transports_reduce {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    Commute P (transportA (normalOfPure S) I) ∧ Commute Q (transportB (normalOfPure S) I) := by
  have hfA : Commute P (flagA (normalOfPure S) I) :=
    (SharpEvents.conditional_flag_sharp S I hS hA hmA P hP).1.symm
  have hmA' : Commute P (magicA (normalOfPure S) I 0) :=
    (SharpEvents.conditional_magic_sharp S I hS hA hmA P hP 0).1.symm
  have hg : Commute Q (S.measurements.bob (I.qB 0) (I.aB 0)) :=
    (bob_reduce S Q hQ.1 _ _ (flagB_projection S I hS hB hmB Q hQ)).symm
  have hr : Commute Q (S.measurements.bob (I.qB 4) (I.aB 2)) :=
    (retained_bob S I hS hB hmB Q hQ).2.1.symm
  have hnproj : Projection (Q*S.measurements.bob (I.qB 0) (I.aB 1)*Q) := by
    rw [← bob_zero_diagonal S I hS hA hB hmA hmB P Q hP hQ]
    have hu := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
    exact ⟨hu.adjoint 0 0,by simpa only [ite_true] using hu.mul 0 0 0 0⟩
  have hn : Commute Q (S.measurements.bob (I.qB 0) (I.aB 1)) := (bob_reduce S Q hQ.1 _ _ hnproj).symm
  exact ⟨(hmA'.mul_right (signA_reduces S I hS hA hB hmA hmB P Q hP hQ 0)).mul_right hfA,
    (((hn.mul_right hr).mul_right (signB_reduces S I hS hA hB hmA hmB P Q hP hQ 0)).mul_right hg).smul_right (Real.sqrt 2:ℂ)⟩

theorem compressed_left_action (v : AB) (P E : Op) (hP : Projection P)
    (hv : left P v=v) (hc : Commute P E) : left (P*E*P) v=left E v := by
  have hh : P*E*P=E*P := by rw [hc.eq,mul_assoc,hP.2]
  rw [hh,left_mul]
  change left E (left P v)=left E v
  rw [hv]

theorem compressed_right_action (v : AB) (Q F : Op) (hQ : Projection Q)
    (hv : right Q v=v) (hc : Commute Q F) : right (Q*F*Q) v=right F v := by
  have hh : Q*F*Q=F*Q := by rw [hc.eq,mul_assoc,hQ.2]
  rw [hh,right_mul]
  change right F (right Q v)=right F v
  rw [hv]

theorem compressed_joint_action (v : AB) (P Q E F : Op) (hP : Projection P) (hQ : Projection Q)
    (hvP : left P v=v) (hvQ : right Q v=v) (hE : Commute P E) (hF : Commute Q F) :
    (left (P*E*P)*right (Q*F*Q)) v=(left E*right F) v := by
  change left (P*E*P) (right (Q*F*Q) v)=left E (right F v)
  rw [compressed_right_action v Q F hQ hvQ hF]
  apply compressed_left_action _ P E hP _ hE
  rw [commute_on,hvP]

#print axioms retained_bob_identification
#print axioms bob_extraction
end Sigma2.ExtractionBlocks
