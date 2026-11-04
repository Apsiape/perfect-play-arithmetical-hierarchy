import Sigma2.MagicRelations
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.PauliExtraction
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral MagicCells MagicRelations

theorem op_neg_mul (A B : Op) : (-A)*B= -(A*B) := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem op_mul_neg (A B : Op) : A*(-B)= -(A*B) := by
  apply ContinuousLinearMap.ext
  intro v
  exact map_neg A (B v)

structure SquareRelations (e : Op) (C : Fin 3 → Fin 3 → Op) : Prop where
  projection : Projection e
  selfadjoint : ∀ x y,star (C x y)=C x y
  right_unit : ∀ x y,C x y*e=C x y
  left_unit : ∀ x y,e*C x y=C x y
  square : ∀ x y,C x y*C x y=e
  row_commute : ∀ x y z,C x y*C x z=C x z*C x y
  col_commute : ∀ x z y,C x y*C z y=C z y*C x y
  row_product : ∀ x,C x 0*(C x 1*C x 2)=e
  col_product : ∀ y,C 0 y*(C 1 y*C 2 y)=(if y.val=2 then (-1:ℂ) else 1) • e

/-- Every relation here is derived from the original strategy on its supplied support. -/
theorem actual_relations {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    SquareRelations (rowActive S I P 0) (rowCell S I P) := by
  have hstar (x y : Fin 3) : star (rowCell S I P x y)=rowCell S I P x y :=
    signed_selfadjoint _ _ (row_sharp S I hS h hm P hP x y)
  have hright (x y : Fin 3) : rowCell S I P x y*rowActive S I P 0=rowCell S I P x y := by
    have hh := line_supported _ false P hP.1
      (compressed_positive P hP.1 (rowPOVM S I x) (fun a => S.measurements.alice_pos _ _))
      (compressed_sum P hP.1 _ (hS.2.1 ⟨x.val,by omega⟩)) (row_sharp S I hS h hm P hP x) y
    change rowCell S I P x y*rowActive S I P x=rowCell S I P x y at hh
    rwa [common_active S I hS h hm P hP x] at hh
  have hsquare (x y : Fin 3) : rowCell S I P x y*rowCell S I P x y=rowActive S I P 0 :=
    (row_square S I hS h hm P hP x y).trans (common_active S I hS h hm P hP x)
  have hestar : star (rowActive S I P 0)=rowActive S I P 0 := by
    calc
      _ = star (rowCell S I P 0 0*rowCell S I P 0 0) := congrArg star (hsquare 0 0).symm
      _ = rowActive S I P 0 := by rw [star_mul,hstar,hsquare]
  have hee : rowActive S I P 0*rowActive S I P 0=rowActive S I P 0 := by
    calc
      _ = (rowCell S I P 0 0*rowCell S I P 0 0)*rowActive S I P 0 := by rw [hsquare]
      _ = rowActive S I P 0 := by rw [mul_assoc,hright,hsquare]
  refine ⟨⟨hestar,hee⟩,hstar,hright,?_,hsquare,
    row_commute S I hS h hm P hP,column_commute S I hS h hm P hP,?_,
    column_product S I hS h hm P hP⟩
  · intro x y
    have hh := congrArg star (hright x y)
    simpa only [star_mul,hestar,hstar] using hh
  · intro x
    exact (MagicCells.row_product S I hS h hm P hP x).trans (common_active S I hS h hm P hP x)

/-- Cancel a third involution using only finite corner algebra. -/
theorem two_product (e A B C : Op) (hB : B*e=B) (hC : e*C=C)
    (hsq : C*C=e) (ht : A*(B*C)=e) : A*B=C := by
  calc
    A*B = (A*B)*e := by rw [mul_assoc,hB]
    _ = (A*(B*C))*C := by rw [← hsq]; noncomm_ring
    _ = C := by rw [ht,hC]

theorem two_product_negative (e A B C : Op) (hB : B*e=B) (hC : e*C=C)
    (hsq : C*C=e) (ht : A*(B*C)= -e) : A*B= -C := by
  calc
    A*B = (A*B)*e := by rw [mul_assoc,hB]
    _ = (A*(B*C))*C := by rw [← hsq]; noncomm_ring
    _ = -C := by rw [ht,op_neg_mul,hC]

/-- The Pauli labelling is fixed: X1=C11, Z1=C00, X2=C01, Z2=C10. -/
theorem anticommute (e : Op) (C : Fin 3 → Fin 3 → Op) (h : SquareRelations e C) :
    C 0 0*C 1 1= -(C 1 1*C 0 0) ∧ C 0 1*C 1 0= -(C 1 0*C 0 1) := by
  have r (x : Fin 3) : C x 0*C x 1=C x 2 :=
    two_product e _ _ _ (h.right_unit x 1) (h.left_unit x 2) (h.square x 2) (h.row_product x)
  have c (y : Fin 3) (hy : y.val≠2) : C 0 y*C 1 y=C 2 y :=
    two_product e _ _ _ (h.right_unit 1 y) (h.left_unit 2 y) (h.square 2 y)
      (by simpa only [hy,ite_false,one_smul] using h.col_product y)
  have c2 : C 0 2*C 1 2= -(C 2 2) :=
    two_product_negative e _ _ _ (h.right_unit 1 2) (h.left_unit 2 2) (h.square 2 2)
      (by have hh := h.col_product 2; norm_num at hh; convert hh using 1 <;> module)
  have cycle : (C 0 0*C 0 1)*(C 1 0*C 1 1)= -((C 0 0*C 1 0)*(C 0 1*C 1 1)) := by
    rw [r 0,r 1,c 0 (by decide),c 1 (by decide),r 2,c2]
  have hBD : C 0 1*C 1 0= -(C 1 0*C 0 1) := by
    have hh := congrArg (fun T : Op => C 0 0*T*C 1 1) cycle
    have hl : C 0 0*((C 0 0*C 0 1)*(C 1 0*C 1 1))*C 1 1=C 0 1*C 1 0 := by
      calc
        _ = (C 0 0*C 0 0)*(C 0 1*C 1 0)*(C 1 1*C 1 1) := by
          try simp only [op_neg_mul,op_mul_neg]
          noncomm_ring
        _ = C 0 1*C 1 0 := by
          rw [h.square,h.square]
          simp only [mul_assoc,h.right_unit]
          rw [← mul_assoc,h.left_unit]
    have hr : C 0 0*(-((C 0 0*C 1 0)*(C 0 1*C 1 1)))*C 1 1= -(C 1 0*C 0 1) := by
      calc
        _ = -((C 0 0*C 0 0)*(C 1 0*C 0 1)*(C 1 1*C 1 1)) := by
          try simp only [op_neg_mul,op_mul_neg]
          noncomm_ring
        _ = -(C 1 0*C 0 1) := by
          rw [h.square,h.square]
          simp only [mul_assoc,h.right_unit]
          rw [← mul_assoc,h.left_unit]
    rwa [hl,hr] at hh
  have hDB : C 1 0*C 0 1= -(C 0 1*C 1 0) := by rw [hBD,neg_neg]
  have comm : (C 0 0*C 1 0)*(C 0 1*C 1 1)=(C 0 1*C 1 1)*(C 0 0*C 1 0) := by
    rw [c 0 (by decide),c 1 (by decide)]
    exact h.row_commute 2 0 1
  have hAE : C 0 0*C 1 1= -(C 1 1*C 0 0) := by
    have hh := congrArg (fun T : Op => C 0 1*T*C 1 0) comm
    have hl : C 0 1*((C 0 0*C 1 0)*(C 0 1*C 1 1))*C 1 0= -(C 0 0*C 1 1) := by
      calc
        _ = (C 0 1*C 0 0)*(C 1 0*C 0 1)*(C 1 1*C 1 0) := by
          try simp only [op_neg_mul,op_mul_neg]
          noncomm_ring
        _ = (C 0 0*C 0 1)*(-(C 0 1*C 1 0))*(C 1 0*C 1 1) := by
          rw [h.row_commute 0 1 0,hDB,h.row_commute 1 1 0]
        _ = -(C 0 0*(C 0 1*C 0 1)*(C 1 0*C 1 0)*C 1 1) := by
          try simp only [op_neg_mul,op_mul_neg]
          noncomm_ring
        _ = -(C 0 0*C 1 1) := by rw [h.square,h.square,h.right_unit,h.right_unit]
    have hr : C 0 1*((C 0 1*C 1 1)*(C 0 0*C 1 0))*C 1 0=C 1 1*C 0 0 := by
      calc
        _ = (C 0 1*C 0 1)*(C 1 1*C 0 0)*(C 1 0*C 1 0) := by
          try simp only [op_neg_mul,op_mul_neg]
          noncomm_ring
        _ = C 1 1*C 0 0 := by
          rw [h.square,h.square]
          simp only [mul_assoc,h.right_unit]
          rw [← mul_assoc,h.left_unit]
    rw [hl,hr] at hh
    rw [← hh,neg_neg]
  exact ⟨hAE,hBD⟩

#print axioms actual_relations
#print axioms anticommute
end Sigma2.PauliExtraction
