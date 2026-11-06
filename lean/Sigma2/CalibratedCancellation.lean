import Sigma2.FilteredSign

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibratedCancellation
open Coefficients TensorLifts PureSupport Preliminaries CoefficientOperator FilteredSign
  CoarseCells DiagonalIdentification MagicRelations

/-- The three positive cases and the negative case force a common Alice sign
and its anticommutation. Only the original Alice dense range is used here. -/
theorem common_sign (v : AB) (P X0 X1 Y0 Y1 D : Op)
    (hr : (coefficient v).range.topologicalClosure=P.range)
    (hX0 : X0*P=X0) (hX1 : X1*P=X1) (hD : D*P=D)
    (h00 : left X0 v=right Y0 v) (h10 : left X1 v=right Y0 v)
    (h01 : left X0 v=right Y1 v)
    (h11 : left X1 (left D v)= -(right Y1 (left D v))) :
    X0=X1 ∧ X0*D= -(D*X0) := by
  have hz : left (X0-X1) v=0 := by
    rw [left_sub,sub_apply,h00,h10,sub_self]
  have hcancel := vector_cancel v P (X0-X1) hr hz
  rw [sub_mul,hX0,hX1] at hcancel
  have he : X0=X1 := sub_eq_zero.mp hcancel
  have hanti : left (X0*D+D*X0) v=0 := by
    rw [left_add,left_mul,left_mul,add_apply]
    change left X0 (left D v)+left D (left X0 v)=0
    rw [he,h11,← he,h01,commute_on D Y1 v,neg_add_cancel]
  have ha := vector_cancel v P (X0*D+D*X0) hr hanti
  rw [add_mul,mul_assoc X0 D P,hD,mul_assoc D X0 P,hX0] at ha
  exact ⟨he,eq_neg_of_add_eq_zero_left ha⟩

#print axioms common_sign
end Sigma2.CalibratedCancellation
