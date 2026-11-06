import Sigma2.CalibrationSharpness

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationSigns
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity
  FilteredSign CalibrationSharpness

def differenceA {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (x : Fin 2) : Op :=
  effectA S I P x 0-effectA S I P x 1
def differenceB {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) (y : Fin 2) : Op :=
  effectB S I Q y 0-effectB S I Q y 1

theorem differenceA_eq {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (x : Fin 2) :
    differenceA S I P x=P*signA S I x*P := by simp only [differenceA,effectA,signA,mul_sub,sub_mul]; rfl
theorem differenceB_eq {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) (y : Fin 2) :
    differenceB S I Q y=Q*signB S I y*Q := by simp only [differenceB,effectB,signB,mul_sub,sub_mul]; rfl

theorem actual_sign_equation {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    left (differenceA S I P x) (signVector S I P Q x y)=
      sigma x y • right (differenceB S I Q y) (signVector S I P Q x y) := by
  have hv := signVector_supported S I hS hA hB hmA hmB P Q hP hQ x y
  have hsA := effects_sumA S I P x
  have hsB := effects_sumB S I Q y
  have heven (hxy : (x.val*y.val)%2=0) :
      left (differenceA S I P x) (signVector S I P Q x y)=
        right (differenceB S I Q y) (signVector S I P Q x y) := by
    have h01 := filtered_forbidden S I hS hA hB hmA hmB P Q hP hQ x y 0 1 (by rw [hxy]; norm_num)
    have h10 := filtered_forbidden S I hS hA hB hmA hmB P Q hP hQ x y 1 0 (by rw [hxy]; norm_num)
    have hh := binary_mirrors _ _ _ _ _ _ _ hv.1 hv.2 hsA hsB h01 h10
    simp only [differenceA,differenceB,left_sub,right_sub,sub_apply,hh.1,hh.2]
  have hodd (hxy : (x.val*y.val)%2=1) :
      left (differenceA S I P x) (signVector S I P Q x y)=
        -(right (differenceB S I Q y) (signVector S I P Q x y)) := by
    have h00 := filtered_forbidden S I hS hA hB hmA hmB P Q hP hQ x y 0 0 (by rw [hxy]; norm_num)
    have h11 := filtered_forbidden S I hS hA hB hmA hmB P Q hP hQ x y 1 1 (by rw [hxy]; norm_num)
    have hh := binary_mirrors _ _ _ _ _ _ _ hv.1 hv.2 hsA ((add_comm _ _).trans hsB) h00 h11
    simp only [differenceA,differenceB,left_sub,right_sub,sub_apply,hh.1,hh.2]
    abel
  fin_cases x <;> fin_cases y
  · simpa [sigma] using heven (by decide)
  · simpa [sigma] using heven (by decide)
  · simpa [sigma] using heven (by decide)
  · simpa [sigma] using hodd (by decide)

theorem alice_sign_properties {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x : Fin 2) :
    let X := differenceA S I P x
    let sx := P*sumA S I x*P
    star X=X ∧ X*X=sx ∧ X*sx=X ∧ sx*X=X := by
  have h0 := alice_sign_sharp S I hS hA hB hmA hmB P Q hP hQ x 0
  have h1 := alice_sign_sharp S I hS hA hB hmA hmB P Q hP hQ x 1
  have hs := (effects_supported S I hS hA hB hmA hmB P Q hP hQ x 0).1
  have hsum := effects_sumA S I P x
  have h01 : effectA S I P x 0*effectA S I P x 1=0 := by
    have hh := congrArg (fun A : Op => effectA S I P x 0*A) hsum
    rw [mul_add,h0.2,hs 0] at hh
    exact add_eq_left.mp hh
  have h10 : effectA S I P x 1*effectA S I P x 0=0 := by
    have hh := congrArg (fun A : Op => effectA S I P x 1*A) hsum
    rw [mul_add,h1.2,hs 1] at hh
    exact add_eq_right.mp hh
  have hself : star (differenceA S I P x)=differenceA S I P x := by
    exact (star_sub (effectA S I P x 0) (effectA S I P x 1)).trans
      (congrArg₂ (fun A B : Op => A-B) h0.1 h1.1)
  have hright : differenceA S I P x*(P*sumA S I x*P)=differenceA S I P x := by
    simp only [differenceA,sub_mul,hs]
  refine ⟨hself,?_,hright,?_⟩
  · simp only [differenceA,sub_mul,mul_sub,h0.2,h1.2,h01,h10,sub_zero,zero_sub,sub_neg_eq_add]
    exact hsum
  · have hh := congrArg star hright
    simpa only [star_mul,hself,(sign_sector S I hS hA hmA P hP x).2.2.1.1] using hh

theorem pull_left (v : AB) (a b X : Op) (hX : X*(a*star a)=X) :
    left (star a*X*a) ((left (star a)*right (star b)) v)=
      (left (star a)*right (star b)) (left X v) := by
  change left (star a*X*a) (left (star a) (right (star b) v))=
    left (star a) (right (star b) (left X v))
  rw [← commute_on X (star b) v]
  change left ((star a*X*a)*star a) (right (star b) v)=
    left (star a*X) (right (star b) v)
  have hh : (star a*X*a)*star a=star a*(X*(a*star a)) := by noncomm_ring
  rw [hh,hX]

theorem pull_right (v : AB) (a b Y : Op) (hY : Y*(b*star b)=Y) :
    right (star b*Y*b) ((left (star a)*right (star b)) v)=
      (left (star a)*right (star b)) (right Y v) := by
  change right (star b*Y*b) (left (star a) (right (star b) v))=
    left (star a) (right (star b) (right Y v))
  rw [← commute_on]
  change left (star a) (right ((star b*Y*b)*star b) v)=
    left (star a) (right (star b*Y) v)
  have hh : (star b*Y*b)*star b=star b*(Y*(b*star b)) := by noncomm_ring
  rw [hh,hY]

#print axioms actual_sign_equation
#print axioms alice_sign_properties
end Sigma2.CalibrationSigns
