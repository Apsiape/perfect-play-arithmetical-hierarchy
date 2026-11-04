import Sigma2.RowRestriction
import Sigma2.RowColumns

open scoped BigOperators
namespace Sigma2.RowConstructionAudit
open Compiler RowGame

/-- The second old Alice question has zero sampling weight and rejects every
answer. Uniform sampling in the extension must leave that pair unconstrained. -/
def zeroWeightGame : Game where
  scenario := ⟨1,0,1,1⟩
  distribution := fun x _ => if x=0 then 1 else 0
  distribution_nonneg := by intro x y; split_ifs <;> norm_num
  distribution_sum := by norm_num [Fin.sum_univ_two, Fin.sum_univ_one]
  accepts := fun x _ _ _ => decide (x=0)

def emptyRows : Rows zeroWeightGame.scenario where
  count := 0
  event := Fin.elim0
  rowCount := 0
  constant := Fin.elim0
  coefficient := Fin.elim0

theorem regression_01 : (game zeroWeightGame emptyRows).accepts
    ((embedding zeroWeightGame emptyRows).qA 1) ((embedding zeroWeightGame emptyRows).qB 0)
    ((embedding zeroWeightGame emptyRows).aA 0) ((embedding zeroWeightGame emptyRows).aB 0)=true := by decide

/-- A named projection with the row E-I=0; its first padding slot is -I. -/
abbrev oneRow : Rows zeroWeightGame.scenario where
  count := 1
  event := fun _ => ⟨0,0,1,1⟩
  rowCount := 1
  constant := fun _ => -1
  coefficient := fun _ _ => 1

theorem regression_02 : (RowSlots.slots oneRow 0).length=16 := by decide
theorem regression_03 : (game zeroWeightGame oneRow).accepts
    ((embedding zeroWeightGame oneRow).qA 0) ((embedding zeroWeightGame oneRow).qB 0)
    ((embedding zeroWeightGame oneRow).aA 0) ((embedding zeroWeightGame oneRow).aB 1)=false := by decide
theorem regression_04 : newRule oneRow (.column 0) (.slot 0 1) 0 3=false := by decide
theorem regression_05 : newRule oneRow (.column 0) (.slot 0 1) 0 4=true := by decide
theorem regression_06 : valid oneRow (.pair 1) 2=false := by decide
theorem regression_07 : newRule oneRow (.column 0) (.global true) 0 0=false := by decide
theorem regression_08 : newRule oneRow (.global true) (.column 0) 0 0=false := by decide

end Sigma2.RowConstructionAudit

