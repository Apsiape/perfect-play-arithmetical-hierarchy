import Sigma2.CalibrationFrame

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationDensity
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame

/-- Faithfulness of h_f direct-sum h_mag/2 on the sign support. The finite
inverse weight below is a bounded two-corner scalar, never a density inverse. -/
theorem half_density_range (T : Op) (h : Density) (P : Op) (hP : SupportOf h P)
    (f m : Op) (hf : Projection f) (hm : Projection m)
    (hfm : f*m=0) (hmf : m*f=0) (hfP : f*P=f) (hmP : m*P=m)
    (hcf : h.op*f=f*h.op) (hcm : h.op*m=m*h.op)
    (hT : T*star T=(f+(1/2:ℂ) • m)*h.op) :
    T.range.topologicalClosure=(f+m).range := by
  have hs : Projection (f+m) := by
    constructor
    · rw [op_star_add,hf.1,hm.1]
    · rw [add_mul,mul_add,mul_add,hf.2,hm.2,hfm,hmf]; abel
  have hsd : (f+m)*(f+(1/2:ℂ) • m)=f+(1/2:ℂ) • m := by
    simp only [add_mul,mul_add,mul_smul_comm,hf.2,hm.2,hfm,hmf,op_smul_zero,zero_add,add_zero]
  have hds : (f+(1/2:ℂ) • m)*(f+m)=f+(1/2:ℂ) • m := by
    simp only [add_mul,mul_add,smul_mul_assoc,hf.2,hm.2,hfm,hmf,op_smul_zero,zero_add,add_zero]
  have hinv : (f+(2:ℂ) • m)*(f+(1/2:ℂ) • m)=f+m := by
    simp only [add_mul,mul_add,mul_smul_comm,smul_mul_assoc,smul_smul,hf.2,hm.2,hfm,hmf,
      op_smul_zero,zero_add,add_zero]
    norm_num
  have hcs : h.op*(f+m)=(f+m)*h.op := by rw [mul_add,add_mul,hcf,hcm]
  apply range_closure T ((f+(1/2:ℂ) • m)*h.op) (f+m) hT hs
  · rw [← mul_assoc,hsd]
  · rw [mul_assoc,hcs,← mul_assoc,hds]
  · intro x hx hz
    apply hP.2.2 x
    · have hPs : P*(f+m)=f+m := by
        have h0 := congrArg star hfP
        have h1 := congrArg star hmP
        have hPf : P*f=f := by simpa only [star_mul,hP.1.1,hf.1] using h0
        have hPm : P*m=m := by simpa only [star_mul,hP.1.1,hm.1] using h1
        rw [mul_add,hPf,hPm]
      have hh := congrArg (fun A : Op => A x) hPs
      change P ((f+m) x)=(f+m) x at hh
      simpa only [hx] using hh
    · have hh := congrArg (fun z : H => (f+(2:ℂ) • m) z) hz
      change ((f+(2:ℂ) • m)*((f+(1/2:ℂ) • m)*h.op)) x=(f+(2:ℂ) • m) 0 at hh
      rw [← mul_assoc,hinv,map_zero,← hcs] at hh
      change h.op ((f+m) x)=0 at hh
      simpa only [hx] using hh

theorem flag_centralizes {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    Commute h.op (P*flagA (normalOfPure S) I*P) :=
  ((support_centralizes h P hP).mul_right
    (SharpEvents.conditional_flag_sharp S I hS h hm P hP).2.2).mul_right (support_centralizes h P hP)

theorem row_centralizes {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (y : Fin 2) :
    Commute h.op (rowSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) y) := by
  have hu (i j : Fin 4) : Commute h.op (actualUnit S I P i j) :=
    (units_analysis S I hS h hm P hP).2.2.2.1 i j
  exact (flag_centralizes S I hS h hm P hP).add_right
    ((((hu 0 0).add_right (hu 1 1)).add_right (((hu 0 1).add_right (hu 1 0)).smul_right (phase y))).smul_right (1/2:ℂ))

/-- The predicate's two sign supports, with the exact column and row labels. -/
theorem actual_sign_supports {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    P*sumA S I x*P=colSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) x ∧
    right (Q*sumB S I y*Q) S.vector=
      left (rowSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) y) S.vector := by
  have hu := units_analysis S I hS hA hmA P hP
  constructor
  · rw [sign_sector_identification S I hS hA hmA P hP x]
    change _=P*flagA (normalOfPure S) I*P+actualUnit S I P (up x) (up x)
    rw [hu.2.2.1]
    rfl
  · have hh := compressed_mirror S.vector P Q _ _ (left_support S hA hmA P hP)
      (right_support S hB hmB Q hQ) (bob_sign_sector S I hS hB hmB Q hQ y).1.symm
    rw [mul_add,add_mul] at hh
    change left (P*flagA (normalOfPure S) I*P+rowDirection S I P y) S.vector=_ at hh
    rw [actual_row_direction S I hS hA hmA P hP y] at hh
    exact hh.symm

def signVector {s} (S : PureStrategy s) (I : FMSInstance s) (P Q : Op) (x y : Fin 2) : AB :=
  (left (P*sumA S I x*P)*right (Q*sumB S I y*Q)) S.vector

theorem signVector_left {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    signVector S I P Q x y=left
      (colSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) x*
        rowSupport (P*flagA (normalOfPure S) I*P) (actualUnit S I P) y) S.vector := by
  have hh := actual_sign_supports S I hS hA hB hmA hmB P Q hP hQ x y
  change left (P*sumA S I x*P) (right (Q*sumB S I y*Q) S.vector)=_
  rw [hh.1,hh.2,left_mul]
  rfl

/-- The filtered vector has precisely the half-weighted marginal used in the
written calibration argument. -/
theorem signVector_covariance {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    coefficient (signVector S I P Q x y)*star (coefficient (signVector S I P Q x y))=
      (P*flagA (normalOfPure S) I*P+(1/2:ℂ) • actualUnit S I P (up x) (up x))*hA.op := by
  let f := P*flagA (normalOfPure S) I*P
  let t := actualUnit S I P
  let sx := colSupport f t x
  let ry := rowSupport f t y
  have hf := actual_frame S I hS hA hmA P hP
  have hu := units_analysis S I hS hA hmA P hP
  have hcs : Commute hA.op sx :=
    (flag_centralizes S I hS hA hmA P hP).add_right (hu.2.2.2.1 (up x) (up x))
  have hcr : Commute hA.op ry := row_centralizes S I hS hA hmA P hP y
  have hsp := col_projection f t hf x
  have hrp := row_projection f t hf y
  have he : coefficient (signVector S I P Q x y)=(sx*ry)*coefficient S.vector := by
    rw [signVector_left S I hS hA hB hmA hmB P Q hP hQ x y,coefficient_left]
  rw [he,star_mul]
  calc
    _ = (sx*ry)*(coefficient S.vector*star (coefficient S.vector))*star (sx*ry) := by noncomm_ring
    _ = (sx*ry)*(hA.op*(ry*sx)) := by
      rw [coefficient_marginal S hA hmA,star_mul,hsp.1,hrp.1]
      noncomm_ring
    _ = (sx*ry)*((ry*sx)*hA.op) := by rw [(hcr.mul_right hcs).eq]
    _ = (sx*(ry*ry)*sx)*hA.op := by noncomm_ring
    _ = (sx*ry*sx)*hA.op := by rw [hrp.2]
    _ = _ := by rw [sandwich f t hf x y]

/-- N3 is available on the full actual Alice sign support of every Omega_xy. -/
theorem signVector_range {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    (coefficient (signVector S I P Q x y)).range.topologicalClosure=
      (P*sumA S I x*P).range := by
  have hu := units_analysis S I hS hA hmA P hP
  have hf := actual_frame S I hS hA hmA P hP
  have hmproj : Projection (actualUnit S I P (up x) (up x)) := by
    rw [hu.2.2.1]
    exact (SharpEvents.conditional_magic_sharp S I hS hA hmA P hP (up x)).2.1
  have hh := half_density_range (coefficient (signVector S I P Q x y)) hA P hP
    (P*flagA (normalOfPure S) I*P) (actualUnit S I P (up x) (up x)) hf.flag hmproj
    (hf.flag_left _ _) (hf.flag_right _ _)
    (by simp only [mul_assoc,hP.1.2])
    (by rw [hu.2.2.1]; simp only [mul_assoc,hP.1.2])
    (flag_centralizes S I hS hA hmA P hP).eq (hu.2.2.2.1 (up x) (up x))
    (signVector_covariance S I hS hA hB hmA hmB P Q hP hQ x y)
  rw [(actual_sign_supports S I hS hA hB hmA hmB P Q hP hQ x y).1]
  exact hh

#print axioms half_density_range
#print axioms actual_sign_supports
#print axioms signVector_left
#print axioms signVector_covariance
#print axioms signVector_range
end Sigma2.CalibrationDensity
