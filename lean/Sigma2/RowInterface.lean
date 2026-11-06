import Sigma2.CompilerBase

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.RowInterface

abbrev coinScenario : Scenario := ⟨0,0,1,1⟩

def half : Op := (1/2:ℂ) • (1:Op)

theorem half_positive : Positive half :=
  ContinuousLinearMap.isPositive_one.smul_of_nonneg (by norm_num [Complex.le_def])

theorem half_add : half+half=1 := by
  ext v k
  simp only [half,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    one_apply_eq_self,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem negative_half_row : (-(1/2:ℂ) • (1:Op))+half=0 := by
  ext v k
  simp only [half,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    one_apply_eq_self,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  norm_num
  <;> ring

def coinMeasurements : Measurements coinScenario := TensorLifts.measurements coinScenario
  (fun _ _ => half) (fun _ _ => half)
  (fun _ _ => half_positive) (fun _ _ => half_positive)
  (fun _ => by
    change (∑ _ : Fin 2,half)=1
    rw [Fin.sum_univ_two]
    exact half_add)
  (fun _ => by
    change (∑ _ : Fin 2,half)=1
    rw [Fin.sum_univ_two]
    exact half_add)

def coinPure : PureStrategy coinScenario where
  measurements := coinMeasurements
  vector := lp.single 2 (0,0) 1
  unit := by simp [lp.norm_single]

def coin : NormalStrategy coinScenario := normalOfPure coinPure

def halfRow : Compiler.Rows coinScenario where
  count := 1
  event := fun _ => ⟨0,0,0,0⟩
  rowCount := 1
  constant := fun _ => -1/2
  coefficient := fun _ _ => 1

theorem half_mirror (v : AB) : TensorLifts.left half v=TensorLifts.right half v := by
  ext ⟨i,j⟩
  rw [TensorLifts.left_apply,TensorLifts.right_apply]
  simp [half,Coefficients.column_apply,Coefficients.row_apply]

theorem left_half : TensorLifts.left half=(1/2:ℂ) • (1:BipOp) := by
  ext v ⟨i,j⟩
  rw [TensorLifts.left_apply]
  simp [half,Coefficients.column_apply]

theorem right_half : TensorLifts.right half=(1/2:ℂ) • (1:BipOp) := by
  ext v ⟨i,j⟩
  rw [TensorLifts.right_apply]
  simp [half,Coefficients.row_apply]

theorem coin_probability (x : QA coinScenario) (y : QB coinScenario)
    (a : AA coinScenario) (b : BB coinScenario) : coin.probability x y a b=1/4 := by
  rw [show coin=normalOfPure coinPure from rfl,normalOfPure_probability]
  change (inner ℂ coinPure.vector
    ((TensorLifts.left half*TensorLifts.right half) coinPure.vector)).re=1/4
  rw [left_half,right_half]
  simp [mul_smul_comm,smul_mul_assoc,smul_smul,inner_smul_right,
    inner_self_eq_norm_sq_to_K,coinPure.unit]
  <;> norm_num

/-- The current RowsHold contract accepts a genuinely nonprojective named effect.
This is a diagnostic of the interface, not a counterexample to the compiler theorem. -/
theorem rows_hold : Compiler.RowsHold halfRow coin := by
  obtain ⟨hA,hB,hmA,hmB⟩ := Preliminaries.marginals_exist coin
  refine ⟨hA,hB,hmA,hmB,?_,?_,?_⟩
  · intro i k hk
    exact half_mirror (coin.vector k)
  · intro r
    change (((( -1/2:ℚ):ℂ) • (1:Op)) + ∑ _ : Fin 1,((1:ℚ):ℂ) • half)*hA.op=0
    rw [Fin.sum_univ_one]
    norm_num only [Rat.cast_one,one_smul]
    rw [negative_half_row,zero_mul]
  · intro r
    change (((( -1/2:ℚ):ℂ) • (1:Op)) + ∑ _ : Fin 1,((1:ℚ):ℂ) • half)*hB.op=0
    rw [Fin.sum_univ_one]
    norm_num only [Rat.cast_one,one_smul]
    rw [negative_half_row,zero_mul]

theorem half_not_projection : ¬ Projection half := by
  intro hh
  have he := congrArg (fun A : Op => A (basis 0) 0) hh.2
  norm_num [half,basis,mul_apply_eq_comp,lp.single_apply,Pi.single_apply] at he

#print axioms rows_hold
#print axioms half_not_projection
end Sigma2.RowInterface



