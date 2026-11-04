import Sigma2.CoefficientSupport
import Sigma2.CalibrationEvents

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.FilteredSign
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicRelations MirrorAlgebra DiagonalIdentification CoefficientOperator

theorem commute_on (A B : Op) (v : AB) : left A (right B v)=right B (left A v) :=
  congrArg (fun T : BipOp => T v) (commute A B)

theorem joint_mul (A B C D : Op) :
    (left A*right B)*(left C*right D)=left (A*C)*right (B*D) := by
  rw [left_mul,right_mul]
  calc
    _ = left A*(right B*left C)*right D := by noncomm_ring
    _ = _ := by rw [← commute C B]; noncomm_ring

theorem compressed_joint (v : AB) (P Q E F : Op)
    (hP : left P v=v) (hQ : right Q v=v) :
    (left (P*E*P)*right (Q*F*Q)) v=
      (left P*right Q) ((left E*right F) v) := by
  rw [← joint_mul,← joint_mul]
  change (left P*right Q) ((left E*right F) ((left P*right Q) v))=_
  have hh : (left P*right Q) v=v := by
    change left P (right Q v)=v
    rw [hQ,hP]
  rw [hh]

@[simp] theorem coefficient_zero : coefficient (0:AB)=0 := by
  apply op_ext
  intro i j
  simp only [entry,coefficient_basis,column_apply,lp.coeFn_zero,Pi.zero_apply,zero_apply]

/-- N3 for any unnormalized filtered vector with the indicated faithful support. -/
theorem vector_cancel (v : AB) (P A : Op)
    (hr : (coefficient v).range.topologicalClosure=P.range)
    (hz : left A v=0) : A*P=0 := by
  apply cancel_on_range A (coefficient v) P hr
  rw [← coefficient_left,hz,coefficient_zero]

/-- Complete binary effects with zero disagreement are mirrors on the filtered
vector. Positivity is used upstream to turn forbidden probabilities into zeros. -/
theorem binary_mirrors (v : AB) (P Q E0 E1 F0 F1 : Op)
    (hvP : left P v=v) (hvQ : right Q v=v)
    (hsE : E0+E1=P) (hsF : F0+F1=Q)
    (h01 : (left E0*right F1) v=0) (h10 : (left E1*right F0) v=0) :
    left E0 v=right F0 v ∧ left E1 v=right F1 v := by
  have he : left E0 v=(left E0*right F0) v := by
    calc
      _ = left E0 (right Q v) := by rw [hvQ]
      _ = _ := by
        rw [← hsF,right_add]
        change left E0 (right F0 v+right F1 v)=_
        have hz : left E0 (right F1 v)=0 := h01
        rw [map_add,hz,add_zero]
        rfl
  have hf : right F0 v=(left E0*right F0) v := by
    calc
      _ = left P (right F0 v) := by
        have hc := congrArg (fun T : BipOp => T v) (commute P F0)
        change left P (right F0 v)=right F0 (left P v) at hc
        rw [hc,hvP]
      _ = _ := by
        rw [← hsE,left_add]
        change left E0 (right F0 v)+left E1 (right F0 v)=_
        rw [show left E1 (right F0 v)=0 from h10,add_zero]
        rfl
  have hm := he.trans hf.symm
  refine ⟨hm,?_⟩
  have hsum : left E0 v+left E1 v=right F0 v+right F1 v := by
    rw [← add_apply,← add_apply,← left_add,← right_add,hsE,hsF,hvP,hvQ]
  rw [hm] at hsum
  exact add_left_cancel hsum

/-- Sharpness from N3 on the sign vector itself. Neither original sign
effect is assumed to be a projection. -/
theorem binary_sharp (v : AB) (P Q E0 E1 F0 F1 : Op)
    (hr : (coefficient v).range.topologicalClosure=P.range)
    (hvP : left P v=v) (hvQ : right Q v=v)
    (hsE : E0+E1=P) (hsF : F0+F1=Q)
    (hEP0 : E0*P=E0) (hEP1 : E1*P=E1)
    (h01 : (left E0*right F1) v=0) (h10 : (left E1*right F0) v=0) :
    E0*E0=E0 ∧ E1*E1=E1 := by
  have hm := binary_mirrors v P Q E0 E1 F0 F1 hvP hvQ hsE hsF h01 h10
  have hz0 : left (E0*E1) v=0 := by
    rw [left_mul]
    change left E0 (left E1 v)=0
    rw [hm.2]
    exact h01
  have hz1 : left (E1*E0) v=0 := by
    rw [left_mul]
    change left E1 (left E0 v)=0
    rw [hm.1]
    exact h10
  have hprod0 := vector_cancel v P (E0*E1) hr hz0
  have hprod1 := vector_cancel v P (E1*E0) hr hz1
  rw [mul_assoc,hEP1] at hprod0
  rw [mul_assoc,hEP0] at hprod1
  constructor
  · have hh := congrArg (fun A : Op => E0*A) hsE
    rw [mul_add,hprod0,add_zero,hEP0] at hh
    exact hh
  · have hh := congrArg (fun A : Op => E1*A) hsE
    rw [mul_add,hprod1,zero_add,hEP1] at hh
    exact hh

#print axioms binary_sharp
end Sigma2.FilteredSign
