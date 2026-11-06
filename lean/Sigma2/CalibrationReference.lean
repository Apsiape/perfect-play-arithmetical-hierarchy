import Sigma2.CalibrationCoordinates
import Sigma2.CalibrationSigns
import Sigma2.VectorCovariance
import Sigma2.CalibratedCancellation

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationReference
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness CalibrationCoordinates CalibrationSigns CalibratedCancellation

def referenceVector {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) : AB :=
  left (P*flagA (normalOfPure S) I*P+invSqrtTwo • actualUnit S I P 0 0) S.vector

def pulledA {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (x : Fin 2) : Op :=
  star (colEmbed (P*flagA (normalOfPure S) I*P) (actualUnit S I P) x)*
    differenceA S I P x*colEmbed (P*flagA (normalOfPure S) I*P) (actualUnit S I P) x
def pulledB {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) (y : Fin 2) : Op :=
  star (rowEmbed (flagB S I Q) (bobUnit S I Q) y)*
    differenceB S I Q y*rowEmbed (flagB S I Q) (bobUnit S I Q) y

theorem reference_covariance {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    coefficient (referenceVector S I P)*star (coefficient (referenceVector S I P))=
      (P*flagA (normalOfPure S) I*P+(1/2:ℂ) • actualUnit S I P 0 0)*h.op := by
  let f := P*flagA (normalOfPure S) I*P
  let t := actualUnit S I P
  let C := f+invSqrtTwo • t 0 0
  have hf : Frame f t := actual_frame S I hS h hm P hP
  have hu := units_analysis S I hS h hm P hP
  have hstar : star C=C := by
    dsimp only [C]
    rw [op_star_add,op_star_smul,hf.flag.1,hf.adjoint,invSqrtTwo_star]
  have hsq : C*C=f+(1/2:ℂ) • t 0 0 := by
    norm_num [C,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,hf.flag.2,
      hf.flag_left,hf.flag_right,hf.mul,invSqrtTwo_sq,op_smul_zero]
  have hc : Commute h.op C := (flag_centralizes S I hS h hm P hP).add_right
    ((show Commute h.op (t 0 0) from hu.2.2.2.1 0 0).smul_right invSqrtTwo)
  change coefficient (left C S.vector)*star (coefficient (left C S.vector))=_
  rw [coefficient_left,star_mul,hstar]
  calc
    _=C*(coefficient S.vector*star (coefficient S.vector))*C := by noncomm_ring
    _=C*h.op*C := by rw [coefficient_marginal S h hm]
    _=(C*C)*h.op := by rw [mul_assoc C h.op C,hc.eq]; noncomm_ring
    _=_ := by rw [hsq]

theorem reference_range {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    (coefficient (referenceVector S I P)).range.topologicalClosure=
      (colSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) 0).range := by
  have hf := actual_frame S I hS h hm P hP
  have hu := units_analysis S I hS h hm P hP
  have hm0 : Projection (actualUnit S I P 0 0) := ⟨hf.adjoint 0 0,by simpa only [ite_true] using hf.mul 0 0 0 0⟩
  exact half_density_range _ h P hP _ _ hf.flag hm0 (hf.flag_left 0 0) (hf.flag_right 0 0)
    (by simp only [mul_assoc,hP.1.2]) (by rw [hu.2.2.1]; simp only [mul_assoc,hP.1.2])
    (flag_centralizes S I hS h hm P hP).eq (hu.2.2.2.1 0 0)
    (reference_covariance S I hS h hm P hP)

/-- The exact four sign equations in the common V coordinates. -/
theorem coordinate_sign_equation {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    let v := left (P*flagA (normalOfPure S) I*P+(sigma x y*invSqrtTwo) • actualUnit S I P 0 0) S.vector
    left (pulledA S I P x) v=sigma x y • right (pulledB S I Q y) v := by
  let f := P*flagA (normalOfPure S) I*P
  let t := actualUnit S I P
  let a := colEmbed f t x
  let b := rowEmbed (flagB S I Q) (bobUnit S I Q) y
  have hf := actual_frame S I hS hA hmA P hP
  have hg := actual_bob_frame S I hS hA hB hmA hmB P Q hP hQ
  have hX : differenceA S I P x*(a*star a)=differenceA S I P x := by
    rw [(col_embed f t hf x).2,← (actual_sign_supports S I hS hA hB hmA hmB P Q hP hQ x y).1]
    exact (alice_sign_properties S I hS hA hB hmA hmB P Q hP hQ x).2.2.1
  have hY : differenceB S I Q y*(b*star b)=differenceB S I Q y := by
    rw [(row_embed _ _ hg y).2,← bob_sign_support S I hS hA hB hmA hmB P Q hP hQ y]
    have hh := (effects_supported S I hS hA hB hmA hmB P Q hP hQ x y).2
    simp only [differenceB,sub_mul,hh]
  have hh := congrArg (fun v : AB => (left (star a)*right (star b)) v)
    (actual_sign_equation S I hS hA hB hmA hmB P Q hP hQ x y)
  rw [map_smul,← pull_left _ a b _ hX,← pull_right _ a b _ hY] at hh
  rw [calibrated_coordinates S I hS hA hB hmA hmB P Q hP hQ x y] at hh
  exact hh

theorem pulledA_supported {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (x : Fin 2) :
    pulledA S I P x*colSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) 0=pulledA S I P x := by
  have hf := actual_frame S I hS h hm P hP
  have ha : colEmbed (P*flagA (normalOfPure S) I*P) (actualUnit S I P) x*
      colSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) 0=
      colEmbed (P*flagA (normalOfPure S) I*P) (actualUnit S I P) x := by
    fin_cases x <;> norm_num [colEmbed,colSupport,up,add_mul,mul_add,hf.flag.2,hf.flag_left,hf.flag_right,hf.mul]
  unfold pulledA
  rw [mul_assoc,ha]

theorem pulledA_zero {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    pulledA S I P 0=differenceA S I P 0 := by
  have hf := actual_frame S I hS hA hmA P hP
  have hp := alice_sign_properties S I hS hA hB hmA hmB P Q hP hQ 0
  have he := (actual_sign_supports S I hS hA hB hmA hmB P Q hP hQ 0 0).1
  have ha : colEmbed (P*flagA (normalOfPure S) I*P) (actualUnit S I P) 0=
      colSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) 0 := rfl
  unfold pulledA
  rw [ha,(col_projection _ _ hf 0).1,← he,hp.2.2.2,hp.2.2.1]

/-- Instantiate the paper's four-case cancellation on the actual reference
vector. The common sign is the compressed original question-3 difference. -/
theorem actual_anticommutation {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    let D := P*flagA (normalOfPure S) I*P-actualUnit S I P 0 0
    differenceA S I P 0*D= -(D*differenceA S I P 0) := by
  let f := P*flagA (normalOfPure S) I*P
  let t := actualUnit S I P
  let D := f-t 0 0
  have hf : Frame f t := actual_frame S I hS hA hmA P hP
  have hD : D*colSupport f t 0=D := by
    norm_num [D,colSupport,up,sub_mul,mul_add,hf.flag.2,hf.flag_left,hf.flag_right,hf.mul]
    abel
  have hdv : left D (referenceVector S I P)=left (f-invSqrtTwo • t 0 0) S.vector := by
    change left D (left (f+invSqrtTwo • t 0 0) S.vector)=_
    change left (D*(f+invSqrtTwo • t 0 0)) S.vector=_
    have hop : D*(f+invSqrtTwo • t 0 0)=f-invSqrtTwo • t 0 0 := by
      simp only [D,sub_mul,mul_add,mul_smul_comm,hf.flag.2,hf.flag_left,hf.flag_right,hf.mul,
        ite_true,op_smul_zero,add_zero,zero_add]
      module
    rw [hop]
  have h00 := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 0 0
  have h10 := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 1 0
  have h01 := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 0 1
  have h11 := coordinate_sign_equation S I hS hA hB hmA hmB P Q hP hQ 1 1
  have hneg : left (f+(sigma 1 1*invSqrtTwo) • t 0 0) S.vector=left D (referenceVector S I P) := by
    rw [hdv]
    have hop : f+(sigma 1 1*invSqrtTwo) • t 0 0=f-invSqrtTwo • t 0 0 := by
      norm_num [sigma]
      module
    rw [hop]
  rw [hneg] at h11
  have hh := common_sign (referenceVector S I P) (colSupport f t 0)
    (pulledA S I P 0) (pulledA S I P 1) (pulledB S I Q 0) (pulledB S I Q 1) D
    (reference_range S I hS hA hmA P hP)
    (pulledA_supported S I hS hA hmA P hP 0) (pulledA_supported S I hS hA hmA P hP 1) hD
    (by simpa [referenceVector,sigma] using h00)
    (by simpa [referenceVector,sigma] using h10)
    (by simpa [referenceVector,sigma] using h01)
    (by simpa [sigma] using h11)
  rw [pulledA_zero S I hS hA hB hmA hmB P Q hP hQ] at hh
  exact hh.2

#print axioms reference_range
#print axioms coordinate_sign_equation
end Sigma2.CalibrationReference
