import Sigma2.UpperSchmidtOperators
import Sigma2.UpperTranspose

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.UpperPOVMTransport

/-- The defect of a contraction is positive. -/
theorem defect_positive (V : Op) (hV : ‖V‖≤1) : Positive (1-star V*V) := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  apply sub_nonneg.mpr
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg (star V*V) (star_mul_self_nonneg V)).mp
  change ‖V.adjoint.comp V‖≤1
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  nlinarith [norm_nonneg V]

/-- Compress a POVM by a contraction and assign its defect to a fixed answer. -/
def effect {ι : Type} [DecidableEq ι] (V : Op) (a₀ a : ι) (A : Op) : Op :=
  star V*A*V + if a=a₀ then 1-star V*V else 0

theorem effect_positive {ι : Type} [DecidableEq ι] (V : Op) (hV : ‖V‖≤1)
    (a₀ a : ι) (A : Op) (hA : Positive A) : Positive (effect V a₀ a A) := by
  have hp : Positive (star V*A*V) := by
    change (star V*A*V).IsPositive
    simpa only [← ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.mul_def,ContinuousLinearMap.comp_assoc]
      using hA.adjoint_conj V
  apply hp.add
  split_ifs
  · exact defect_positive V hV
  · exact ContinuousLinearMap.isPositive_zero

theorem effect_sum {ι : Type} [Fintype ι] [DecidableEq ι] (V : Op) (a₀ : ι)
    (A : ι → Op) (hA : ∑ a,A a=1) : ∑ a,effect V a₀ a (A a)=1 := by
  simp only [effect,Finset.sum_add_distrib,← Finset.sum_mul,← Finset.mul_sum,hA,mul_one]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  abel

def measurements {s} (M : Measurements s) (U V : Op) (hU : ‖U‖≤1) (hV : ‖V‖≤1) : Measurements s :=
  TensorLifts.measurements s (fun x a => effect U 0 a (M.alice x a))
    (fun y b => effect V 0 b (M.bob y b))
    (fun x a => effect_positive U hU 0 a _ (M.alice_pos x a))
    (fun y b => effect_positive V hV 0 b _ (M.bob_pos y b))
    (fun x => effect_sum U 0 _ (M.alice_sum x))
    (fun y => effect_sum V 0 _ (M.bob_sum y))

/-- Adjoint compatibility for the actual completed first-factor lift. -/
theorem left_adjoint (A : Op) : (TensorLifts.left A).adjoint=TensorLifts.left A.adjoint := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right,TensorLifts.inner_columns,TensorLifts.inner_columns]
  simp only [TensorLifts.column_left]
  exact tsum_congr (fun j => (ContinuousLinearMap.adjoint_inner_right A _ _).symm)

/-- Adjoint compatibility for the actual completed second-factor lift. -/
theorem right_adjoint (A : Op) : (TensorLifts.right A).adjoint=TensorLifts.right A.adjoint := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right,TensorLifts.inner_rows,TensorLifts.inner_rows]
  simp only [TensorLifts.row_right]
  exact tsum_congr (fun j => (ContinuousLinearMap.adjoint_inner_right A _ _).symm)

theorem left_add (A B : Op) : TensorLifts.left (A+B)=TensorLifts.left A+TensorLifts.left B := by
  apply ContinuousLinearMap.ext
  intro v
  ext ij
  rcases ij with ⟨i,j⟩
  simp only [TensorLifts.left_apply,add_apply,lp.coeFn_add,Pi.add_apply]

theorem right_add (A B : Op) : TensorLifts.right (A+B)=TensorLifts.right A+TensorLifts.right B := by
  apply ContinuousLinearMap.ext
  intro v
  ext ij
  rcases ij with ⟨i,j⟩
  simp only [TensorLifts.right_apply,add_apply,lp.coeFn_add,Pi.add_apply]

/-- The compressed tensor joint operator is the pullback of the original one. -/
theorem joint_pullback (U V A B : Op) :
    TensorLifts.left (star U*A*U)*TensorLifts.right (star V*B*V)=
      star (TensorLifts.left U*TensorLifts.right V)*
        (TensorLifts.left A*TensorLifts.right B)*(TensorLifts.left U*TensorLifts.right V) := by
  simp only [star_mul,ContinuousLinearMap.star_eq_adjoint,left_adjoint,right_adjoint,
    TensorLifts.left_mul,TensorLifts.right_mul]
  rw [show TensorLifts.left U.adjoint*TensorLifts.left A*TensorLifts.left U*
    (TensorLifts.right V.adjoint*TensorLifts.right B*TensorLifts.right V)=
    TensorLifts.left U.adjoint*TensorLifts.left A*
      (TensorLifts.left U*TensorLifts.right V.adjoint)*TensorLifts.right B*TensorLifts.right V by noncomm_ring]
  rw [TensorLifts.commute U V.adjoint]
  rw [show TensorLifts.left U.adjoint*TensorLifts.left A*
    (TensorLifts.right V.adjoint*TensorLifts.left U)*TensorLifts.right B*TensorLifts.right V=
    (TensorLifts.left U.adjoint*TensorLifts.left A*TensorLifts.right V.adjoint)*
      (TensorLifts.left U*TensorLifts.right B)*TensorLifts.right V by noncomm_ring]
  rw [TensorLifts.commute U B]
  rw [show TensorLifts.left U.adjoint*TensorLifts.left A*TensorLifts.right V.adjoint=
    TensorLifts.right V.adjoint*(TensorLifts.left U.adjoint*TensorLifts.left A) from
      TensorLifts.commute (U.adjoint*A) V.adjoint |>.trans (by rw [TensorLifts.left_mul])]
  noncomm_ring

@[simp] theorem left_zero : TensorLifts.left 0=0 := by
  ext v ij
  rcases ij with ⟨i,j⟩
  simp [TensorLifts.left_apply]

@[simp] theorem right_zero : TensorLifts.right 0=0 := by
  ext v ij
  rcases ij with ⟨i,j⟩
  simp [TensorLifts.right_apply]

theorem left_effect_apply {ι : Type} [DecidableEq ι] (U A : Op) (a₀ a : ι) (z : AB)
    (hz : TensorLifts.left (1-star U*U) z=0) :
    TensorLifts.left (effect U a₀ a A) z=TensorLifts.left (star U*A*U) z := by
  by_cases ha : a=a₀
  · simp [effect,ha,left_add,hz]
  · simp [effect,ha]

theorem right_effect_apply {ι : Type} [DecidableEq ι] (V A : Op) (a₀ a : ι) (z : AB)
    (hz : TensorLifts.right (1-star V*V) z=0) :
    TensorLifts.right (effect V a₀ a A) z=TensorLifts.right (star V*A*V) z := by
  by_cases ha : a=a₀
  · simp [effect,ha,right_add,hz]
  · simp [effect,ha]

/-- Exact preservation of each event by the normalized POVM pullback, on a state
supported where the two contraction defects vanish. -/
theorem event_inner {s} (M : Measurements s) (U V : Op) (hU : ‖U‖≤1) (hV : ‖V‖≤1)
    (z : AB) (hDU : TensorLifts.left (1-star U*U) z=0)
    (hDV : TensorLifts.right (1-star V*V) z=0) (x : QA s) (y : QB s) (a : AA s) (b : BB s) :
    inner ℂ z (((measurements M U V hU hV).left x a*(measurements M U V hU hV).right y b) z)=
      inner ℂ ((TensorLifts.left U*TensorLifts.right V) z)
        ((M.left x a*M.right y b) ((TensorLifts.left U*TensorLifts.right V) z)) := by
  have hR := right_effect_apply V (M.bob y b) (0 : BB s) b z hDV
  have hD : TensorLifts.left (1-star U*U) (TensorLifts.right (star V*M.bob y b*V) z)=0 := by
    have hh := congrArg (fun A : BipOp => A z)
      (TensorLifts.commute (1-star U*U) (star V*M.bob y b*V))
    change TensorLifts.left (1-star U*U) (TensorLifts.right (star V*M.bob y b*V) z)=
      TensorLifts.right (star V*M.bob y b*V) (TensorLifts.left (1-star U*U) z) at hh
    simpa only [hDU,map_zero] using hh
  change inner ℂ z (TensorLifts.left (effect U 0 a (M.alice x a))
    (TensorLifts.right (effect V 0 b (M.bob y b)) z))=_
  rw [hR,left_effect_apply U (M.alice x a) (0 : AA s) a _ hD]
  change inner ℂ z ((TensorLifts.left (star U*M.alice x a*U)*
    TensorLifts.right (star V*M.bob y b*V)) z)=_
  rw [joint_pullback]
  change inner ℂ z (star (TensorLifts.left U*TensorLifts.right V)
    ((TensorLifts.left (M.alice x a)*TensorLifts.right (M.bob y b))
      ((TensorLifts.left U*TensorLifts.right V) z)))=_
  rw [ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right,
    ← TensorLifts.measurements_left,← TensorLifts.measurements_right]

end Sigma2.UpperPOVMTransport



