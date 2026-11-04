import Sigma2.CalibrationSharpness

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationCoordinates
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness

def flagB {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) : Op :=
  Q*S.measurements.bob (I.qB 0) (I.aB 0)*Q

theorem flagB_projection {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalB (normalOfPure S) h) (Q : Op) (hQ : SupportOf h Q) :
    Projection (flagB S I Q) := by
  have hh := col_sharp S I hS h hm Q hQ 0 0 0
  simpa [coarse,compressed,colPOVM,cellClass,cellSign,Fin.sum_univ_succ,flagB] using hh

theorem flag_pair {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    AdjointMirror S.vector (P*flagA (normalOfPure S) I*P) (flagB S I Q) := by
  apply adjointMirror_self _ _ _ (actual_frame S I hS hA hmA P hP).flag.1
    (flagB_projection S I hS hB hmB Q hQ).1
  exact compressed_mirror S.vector P Q _ _ (left_support S hA hmA P hP)
    (right_support S hB hmB Q hQ) (flag_mirror S I hS hA hmA P hP)

theorem actual_bob_frame {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    Frame (flagB S I Q) (bobUnit S I Q) := by
  have hf := actual_frame S I hS hA hmA P hP
  have hp := flag_pair S I hS hA hB hmA hmB P Q hP hQ
  have hu := bob_units_analysis S I hS hA hB hmA hmB P Q hP hQ
  have hm := units_mirror S I hS hA hB hmA hmB P Q hP hQ
  have hs := bobUnit_supported S I Q hQ.1
  refine ⟨flagB_projection S I hS hB hmB Q hQ,hu.1,hu.2,?_,?_⟩
  · intro i j
    have hh := mirror_mul S.vector _ _ _ _ (hm j i).1 hp.1
    rw [hf.flag_right,left_zero,zero_apply] at hh
    exact right_local_eq S hB hmB Q hQ _ _ (by rw [mul_assoc,hs]) (by simp)
      (by simpa only [right_zero,zero_apply] using hh.symm)
  · intro i j
    have hh := mirror_mul S.vector _ _ _ _ hp.1 (hm j i).1
    rw [hf.flag_left,left_zero,zero_apply] at hh
    exact right_local_eq S hB hmB Q hQ _ _
      (by simp only [flagB,mul_assoc,hQ.1.2]) (by simp)
      (by simpa only [right_zero,zero_apply] using hh.symm)

theorem row_support_mirror (v : AB) (f g : Op) (t u : Fin 4 → Fin 4 → Op)
    (hf : left f v=right g v) (ht : ∀ i j,left (t i j) v=right (u j i) v) (y : Fin 2) :
    left (rowSupport f t y) v=right (rowSupport g u y) v := by
  simp only [rowSupport,left_add,right_add,left_smul,right_smul,add_apply,smul_apply,hf,ht]
  congr 2
  abel

theorem bob_sign_support {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (y : Fin 2) :
    Q*sumB S I y*Q=rowSupport (flagB S I Q) (bobUnit S I Q) y := by
  have hm := units_mirror S I hS hA hB hmA hmB P Q hP hQ
  have hf := flag_pair S I hS hA hB hmA hmB P Q hP hQ
  have hh := (actual_sign_supports S I hS hA hB hmA hmB P Q hP hQ 0 y).2
  have he := row_support_mirror S.vector _ _ _ _ hf.1 (fun i j => (hm i j).1) y
  apply right_local_eq S hB hmB Q hQ _ _ (by simp only [mul_assoc,hQ.1.2]) _ (hh.trans he)
  simp only [rowSupport,add_mul,smul_mul_assoc,bobUnit_supported S I Q hQ.1,
    flagB,mul_assoc,hQ.1.2]

theorem row_embed_reverse_mirror (v : AB) (f g : Op) (t u : Fin 4 → Fin 4 → Op)
    (hg : Frame g u) (hf : left f v=right g v)
    (ht : ∀ i j,left (t i j) v=right (u j i) v) (y : Fin 2) :
    left (rowEmbed f t y) v=right (star (rowEmbed g u y)) v := by
  have hphase : star (phase y)=phase y := by fin_cases y <;> norm_num [phase]
  simp only [rowEmbed]
  rw [op_star_add,op_star_smul,op_star_add,op_star_smul,hg.flag.1,hg.adjoint,hg.adjoint,
    invSqrtTwo_star,hphase]
  simp only [rowEmbed,left_add,right_add,left_smul,right_smul,add_apply,smul_apply,hf,ht]

theorem col_embed_reduces (f : Op) (t : Fin 4 → Fin 4 → Op) (h : Frame f t) (x : Fin 2) :
    star (colEmbed f t x)*colSupport f t x=star (colEmbed f t x) := by
  simp only [colEmbed,colSupport,op_star_add,h.flag.1,h.adjoint,add_mul,mul_add,
    h.flag.2,h.flag_left,h.flag_right,h.mul,ite_true,add_zero,zero_add]

theorem row_embed_reduces (f : Op) (t : Fin 4 → Fin 4 → Op) (h : Frame f t) (y : Fin 2) :
    star (rowEmbed f t y)*rowSupport f t y=star (rowEmbed f t y) := by
  have he := row_embed f t h y
  have hs : rowEmbed f t y*colSupport f t 0=rowEmbed f t y := by
    norm_num [rowEmbed,colSupport,up,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      h.flag.2,h.flag_left,h.flag_right,h.mul,op_smul_zero]
  have hss := congrArg star hs
  rw [star_mul,(col_projection f t h 0).1] at hss
  rw [← he.2,← mul_assoc,he.1,hss]

/-- The four actual filtered vectors, in the common V coordinates, are
Omega_ff + sigma_xy omega_mag/sqrt(2), with the original fixed unit labels. -/
theorem calibrated_coordinates {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    let f := P*flagA (normalOfPure S) I*P
    let t := actualUnit S I P
    (left (star (colEmbed f t x))*right (star (rowEmbed (flagB S I Q) (bobUnit S I Q) y)))
      (signVector S I P Q x y)=left (f+(sigma x y*invSqrtTwo) • t 0 0) S.vector := by
  have hf := actual_frame S I hS hA hmA P hP
  have hg := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have hp := flag_pair S I hS hA hB hmA hmB P Q hP hQ
  have hm := units_mirror S I hS hA hB hmA hmB P Q hP hQ
  have he := (actual_sign_supports S I hS hA hB hmA hmB P Q hP hQ x y).1
  let f := P*flagA (normalOfPure S) I*P
  let t := actualUnit S I P
  let a := colEmbed f t x
  let b := rowEmbed (flagB S I Q) (bobUnit S I Q) y
  dsimp only
  unfold signVector
  change ((left (star a)*right (star b))*(left (P*sumA S I x*P)*right (Q*sumB S I y*Q))) S.vector=_
  rw [joint_mul,he,bob_sign_support S I hS hA hB hmA hmB P Q hP hQ y,
    col_embed_reduces _ _ hf x,row_embed_reduces _ _ hg y]
  change left (star a) (right (star b) S.vector)=_
  rw [← row_embed_reverse_mirror S.vector _ _ _ _ hg hp.1 (fun i j => (hm i j).1) y]
  change left (star (colEmbed f t x)*rowEmbed f t y) S.vector=_
  rw [overlap _ _ hf x y]

#print axioms actual_bob_frame
#print axioms bob_sign_support
#print axioms calibrated_coordinates
end Sigma2.CalibrationCoordinates
