import Sigma2.ActualCalibration

set_option synthInstance.maxHeartbeats 10000
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.BobCalibration
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness CalibrationCoordinates CalibrationSigns CalibrationReference ActualCalibration

theorem bob_mirror_centralizes {s} (S : PureStrategy s) (hB : Density)
    (hmB : MarginalB (normalOfPure S) hB) (A B : Op)
    (hA : star A=A) (hBsa : star B=B) (hm : left A S.vector=right B S.vector) :
    Commute hB.op B := by
  have hswap := congrArg swap hm
  have he : left B (swap S.vector)=right A (swap S.vector) := by
    simpa only [PureTransfer.swap_left,PureTransfer.swap_right] using hswap.symm
  have hh := mirrors_covariance (swap S.vector) B A hBsa hA he
  have hc := marginalA_covariance (PureTransfer.flipPure S) hB hmB
  change hB.op=covariance (column (swap S.vector)) at hc
  rw [← hc] at hh
  exact hh.symm

theorem bob_reference_range {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    (coefficient (swap (referenceVector S I P))).range.topologicalClosure=
      (colSupport (flagB S I Q) (bobUnit S I Q) 0).range := by
  let f := P*flagA (normalOfPure S) I*P
  let t := actualUnit S I P
  let g := flagB S I Q
  let u := bobUnit S I Q
  let C := g+invSqrtTwo • u 0 0
  have hf : Frame f t := actual_frame S I hS hA hmA P hP
  have hg : Frame g u := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have hp := flag_pair S I hS hA hB hmA hmB P Q hP hQ
  have hm := units_mirror S I hS hA hB hmA hmB P Q hP hQ
  have hgc : Commute hB.op g := bob_mirror_centralizes S hB hmB f g hf.flag.1 hg.flag.1 hp.1
  have hnc : Commute hB.op (u 0 0) := bob_mirror_centralizes S hB hmB (t 0 0) (u 0 0)
    (hf.adjoint 0 0) (hg.adjoint 0 0) (hm 0 0).1
  have hmatch := (adjointMirror_add S.vector _ _ _ _ hp
    (adjointMirror_smul S.vector _ _ invSqrtTwo (hm 0 0))).1
  have hv : swap (referenceVector S I P)=left C (swap S.vector) := by
    change swap (left (f+invSqrtTwo • t 0 0) S.vector)=_
    rw [hmatch,PureTransfer.swap_right]
  have hstar : star C=C := by
    dsimp only [C]
    rw [op_star_add,op_star_smul,hg.flag.1,hg.adjoint,invSqrtTwo_star]
  have hsq : C*C=g+(1/2:ℂ) • u 0 0 := by
    norm_num [C,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,hg.flag.2,
      hg.flag_left,hg.flag_right,hg.mul,invSqrtTwo_sq,op_smul_zero]
  have hc : Commute hB.op C := hgc.add_right (hnc.smul_right invSqrtTwo)
  have hcov : coefficient (swap (referenceVector S I P))*star (coefficient (swap (referenceVector S I P)))=
      (g+(1/2:ℂ) • u 0 0)*hB.op := by
    rw [hv,coefficient_left,star_mul,hstar]
    calc
      _=C*(coefficient (swap S.vector)*star (coefficient (swap S.vector)))*C := by noncomm_ring
      _=C*hB.op*C := by
        have hh : coefficient (swap S.vector)*star (coefficient (swap S.vector))=hB.op :=
          coefficient_marginal (PureTransfer.flipPure S) hB hmB
        rw [hh]
      _=(C*C)*hB.op := by rw [mul_assoc C hB.op C,hc.eq]; noncomm_ring
      _=_ := by rw [hsq]
  have hn : Projection (u 0 0) := ⟨hg.adjoint 0 0,by simpa only [ite_true] using hg.mul 0 0 0 0⟩
  exact half_density_range _ hB Q hQ g (u 0 0) hg.flag hn (hg.flag_left 0 0) (hg.flag_right 0 0)
    (by simp only [g,flagB,mul_assoc,hQ.1.2]) (bobUnit_supported S I Q hQ.1 0 0) hgc.eq hnc.eq hcov

theorem signVector_from_reference {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (y : Fin 2) :
    signVector S I P Q 0 y=right (rowEmbed (flagB S I Q) (bobUnit S I Q) y) (referenceVector S I P) := by
  let a := colSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) 0
  let b := rowEmbed (flagB S I Q) (bobUnit S I Q) y
  have hg := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have he := calibrated_coordinates S I hS hA hB hmA hmB P Q hP hQ 0 y
  dsimp only at he
  have hs := signVector_supported S I hS hA hB hmA hmB P Q hP hQ 0 y
  rw [(actual_sign_supports S I hS hA hB hmA hmB P Q hP hQ 0 y).1] at hs
  have ha : colEmbed (P*flagA (normalOfPure S) I*P) (actualUnit S I P) 0=a := rfl
  rw [ha,(col_projection _ _ (actual_frame S I hS hA hmA P hP) 0).1] at he
  have he' : right (star b) (signVector S I P Q 0 y)=referenceVector S I P := by
    have ht : left a (right (star b) (signVector S I P Q 0 y))=
        right (star b) (signVector S I P Q 0 y) := by rw [commute_on,hs.1]
    change left a (right (star b) (signVector S I P Q 0 y))=_ at he
    rw [ht] at he
    fin_cases y <;> simpa [referenceVector,sigma] using he
  have hh := congrArg (right b) he'
  change right (b*star b) (signVector S I P Q 0 y)=_ at hh
  rw [(row_embed _ _ hg y).2,← bob_sign_support S I hS hA hB hmA hmB P Q hP hQ y,hs.2] at hh
  exact hh

/-- Bob's N3 on the original local sign support, with no injectivity on a
Bob-environment tensor cut. -/
theorem bob_sign_cancel {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (y : Fin 2) (A : Op)
    (hz : right A (signVector S I P Q 0 y)=0) : A*(Q*sumB S I y*Q)=0 := by
  let b := rowEmbed (flagB S I Q) (bobUnit S I Q) y
  have hg := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have hs : b*colSupport (flagB S I Q) (bobUnit S I Q) 0=b := by
    norm_num [b,rowEmbed,colSupport,up,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      hg.flag.2,hg.flag_left,hg.flag_right,hg.mul,op_smul_zero]
  have hzero : left (A*b) (swap (referenceVector S I P))=0 := by
    have hh := congrArg swap hz
    rw [signVector_from_reference S I hS hA hB hmA hmB P Q hP hQ y,
      PureTransfer.swap_right,PureTransfer.swap_right,map_zero] at hh
    exact hh
  have hh := vector_cancel (swap (referenceVector S I P))
    (colSupport (flagB S I Q) (bobUnit S I Q) 0) (A*b)
    (bob_reference_range S I hS hA hB hmA hmB P Q hP hQ) hzero
  rw [mul_assoc,hs] at hh
  rw [bob_sign_support S I hS hA hB hmA hmB P Q hP hQ y,← (row_embed _ _ hg y).2,← mul_assoc,hh,zero_mul]

theorem bob_sign_sharp {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (y b : Fin 2) :
    Projection (effectB S I Q y b) := by
  let v := signVector S I P Q 0 y
  have hv := signVector_supported S I hS hA hB hmA hmB P Q hP hQ 0 y
  have hs := (effects_supported S I hS hA hB hmA hmB P Q hP hQ 0 y).2
  have h01 := filtered_forbidden S I hS hA hB hmA hmB P Q hP hQ 0 y 0 1 (by norm_num)
  have h10 := filtered_forbidden S I hS hA hB hmA hmB P Q hP hQ 0 y 1 0 (by norm_num)
  have hm := binary_mirrors _ _ _ _ _ _ _ hv.1 hv.2 (effects_sumA S I P 0) (effects_sumB S I Q y) h01 h10
  have hz01 : right (effectB S I Q y 0*effectB S I Q y 1) v=0 := by
    change right (effectB S I Q y 0) (right (effectB S I Q y 1) v)=0
    rw [← hm.2,← commute_on]
    exact h10
  have hz10 : right (effectB S I Q y 1*effectB S I Q y 0) v=0 := by
    change right (effectB S I Q y 1) (right (effectB S I Q y 0) v)=0
    rw [← hm.1,← commute_on]
    exact h01
  have hp01 := bob_sign_cancel S I hS hA hB hmA hmB P Q hP hQ y _ hz01
  have hp10 := bob_sign_cancel S I hS hA hB hmA hmB P Q hP hQ y _ hz10
  rw [mul_assoc,hs 1] at hp01
  rw [mul_assoc,hs 0] at hp10
  have hsq0 : effectB S I Q y 0*effectB S I Q y 0=effectB S I Q y 0 := by
    have hh := congrArg (fun A : Op => effectB S I Q y 0*A) (effects_sumB S I Q y)
    rw [mul_add,hp01,add_zero,hs 0] at hh
    exact hh
  have hsq1 : effectB S I Q y 1*effectB S I Q y 1=effectB S I Q y 1 := by
    have hh := congrArg (fun A : Op => effectB S I Q y 1*A) (effects_sumB S I Q y)
    rw [mul_add,hp10,zero_add,hs 1] at hh
    exact hh
  have hp : Positive (effectB S I Q y b) := compressed_positive Q hQ.1
    (fun b : Fin 6 => S.measurements.bob (I.qB (signQuestion y)) (I.aB b))
    (fun b => S.measurements.bob_pos _ _) ⟨b.val,by omega⟩
  refine ⟨hp.isSelfAdjoint.star_eq,?_⟩
  fin_cases b
  · exact hsq0
  · exact hsq1

#print axioms bob_reference_range
#print axioms bob_sign_cancel
#print axioms bob_sign_sharp
end Sigma2.BobCalibration
