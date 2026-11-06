import Sigma2.CalibrationDensity
import Sigma2.FilteredSign

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationSharpness
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame CalibrationDensity FilteredSign

def effectA {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (x a : Fin 2) : Op :=
  P*S.measurements.alice (I.qA (signQuestion x)) (I.aA ⟨a.val,by omega⟩)*P
def effectB {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) (y b : Fin 2) : Op :=
  Q*S.measurements.bob (I.qB (signQuestion y)) (I.aB ⟨b.val,by omega⟩)*Q

theorem effects_sumA {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (x : Fin 2) :
    effectA S I P x 0+effectA S I P x 1=P*sumA S I x*P := by
  simp only [effectA,sumA,mul_add,add_mul]
  rfl
theorem effects_sumB {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) (y : Fin 2) :
    effectB S I Q y 0+effectB S I Q y 1=Q*sumB S I y*Q := by
  simp only [effectB,sumB,mul_add,add_mul]
  rfl

theorem binary_supported (P E0 E1 : Op) (hP : Projection P)
    (h0 : Positive E0) (h1 : Positive E1) (hs : E0+E1=P) :
    (E0*P=E0 ∧ P*E0=E0) ∧ (E1*P=E1 ∧ P*E1=E1) := by
  constructor
  · exact positive_below_projection E0 P h0 hP (by rw [← hs]; simpa only [add_sub_cancel_left] using h1)
  · exact positive_below_projection E1 P h1 hP (by rw [← hs]; simpa only [add_sub_cancel_right] using h0)

theorem effects_supported {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    (∀ a,effectA S I P x a*(P*sumA S I x*P)=effectA S I P x a) ∧
      (∀ b,effectB S I Q y b*(Q*sumB S I y*Q)=effectB S I Q y b) := by
  have hAP (a : Fin 2) : Positive (effectA S I P x a) :=
    compressed_positive P hP.1
      (fun a : Fin 6 => S.measurements.alice (I.qA (signQuestion x)) (I.aA a))
      (fun a => S.measurements.alice_pos _ _) ⟨a.val,by omega⟩
  have hBP (b : Fin 2) : Positive (effectB S I Q y b) :=
    compressed_positive Q hQ.1
      (fun b : Fin 6 => S.measurements.bob (I.qB (signQuestion y)) (I.aB b))
      (fun b => S.measurements.bob_pos _ _) ⟨b.val,by omega⟩
  have ha := binary_supported _ _ _ (sign_sector S I hS hA hmA P hP x).2.2.1
    (hAP 0) (hAP 1) (effects_sumA S I P x)
  have hb := binary_supported _ _ _ (bob_sign_sector S I hS hB hmB Q hQ y).2.2
    (hBP 0) (hBP 1) (effects_sumB S I Q y)
  constructor
  · intro a; fin_cases a; exact ha.1.1; exact ha.2.1
  · intro b; fin_cases b; exact hb.1.1; exact hb.2.1

theorem signVector_supported {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 2) :
    left (P*sumA S I x*P) (signVector S I P Q x y)=signVector S I P Q x y ∧
      right (Q*sumB S I y*Q) (signVector S I P Q x y)=signVector S I P Q x y := by
  have ha := (sign_sector S I hS hA hmA P hP x).2.2.1.2
  have hb := (bob_sign_sector S I hS hB hmB Q hQ y).2.2.2
  constructor
  · change left (P*sumA S I x*P* (P*sumA S I x*P)) (right (Q*sumB S I y*Q) S.vector)=_
    rw [ha]
    rfl
  · change right (Q*sumB S I y*Q) (left (P*sumA S I x*P) (right (Q*sumB S I y*Q) S.vector))=_
    rw [← commute_on]
    change left (P*sumA S I x*P) (right ((Q*sumB S I y*Q)*(Q*sumB S I y*Q)) S.vector)=_
    rw [hb]
    rfl

theorem filtered_forbidden {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y a b : Fin 2)
    (hab : (a.val+b.val)%2≠(x.val*y.val)%2) :
    (left (effectA S I P x a)*right (effectB S I Q y b)) (signVector S I P Q x y)=0 := by
  have hs := effects_supported S I hS hA hB hmA hmB P Q hP hQ x y
  change ((left (effectA S I P x a)*right (effectB S I Q y b))*
    (left (P*sumA S I x*P)*right (Q*sumB S I y*Q))) S.vector=0
  rw [joint_mul,hs.1 a,hs.2 b]
  rw [effectA,effectB,compressed_joint S.vector P Q _ _
    (left_support S hA hmA P hP) (right_support S hB hmB Q hQ)]
  rw [forbidden_sign_zero S I hS x y a b hab,map_zero]

/-- Actual individual Alice sign effects are sharp, by N3 on Omega_x0.
No sharpness premise on either original sign effect is used. -/
theorem alice_sign_sharp {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x a : Fin 2) :
    Projection (effectA S I P x a) := by
  have hs := signVector_supported S I hS hA hB hmA hmB P Q hP hQ x 0
  have he := effects_supported S I hS hA hB hmA hmB P Q hP hQ x 0
  have hz01 := filtered_forbidden S I hS hA hB hmA hmB P Q hP hQ x 0 0 1 (by norm_num)
  have hz10 := filtered_forbidden S I hS hA hB hmA hmB P Q hP hQ x 0 1 0 (by norm_num)
  have hh := binary_sharp (signVector S I P Q x 0) (P*sumA S I x*P) (Q*sumB S I 0*Q)
    (effectA S I P x 0) (effectA S I P x 1) (effectB S I Q 0 0) (effectB S I Q 0 1)
    (signVector_range S I hS hA hB hmA hmB P Q hP hQ x 0) hs.1 hs.2
    (effects_sumA S I P x) (effects_sumB S I Q 0) (he.1 0) (he.1 1) hz01 hz10
  have hp : Positive (effectA S I P x a) :=
    compressed_positive P hP.1
      (fun a : Fin 6 => S.measurements.alice (I.qA (signQuestion x)) (I.aA a))
      (fun a => S.measurements.alice_pos _ _) ⟨a.val,by omega⟩
  refine ⟨hp.isSelfAdjoint.star_eq,?_⟩
  fin_cases a
  · exact hh.1
  · exact hh.2

#print axioms alice_sign_sharp
end Sigma2.CalibrationSharpness
