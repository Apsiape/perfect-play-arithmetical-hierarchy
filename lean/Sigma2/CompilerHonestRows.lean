import Sigma2.CompilerHonestListRows
import Sigma2.CompilerApproxDictionaryEnergy

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestRows
open Compiler CompilerScaffold CompilerApproxRows CompilerApproxDictionaryIndex CompilerEventLoss
  CompilerHonestListRows CompilerHonestPolynomial CompilerHonestState CompilerHonestFMSLift
  CompilerHonestPregameBase CoefficientOperator TensorLifts
attribute [local irreducible] names rowList words polynomials structuralPolynomials applicationPolynomials rowsBefore

def numbered {P : Presentation} (R : StructuralRealization P) (i : Fin (rows P).count) : Op :=
  CompilerOrientedProjections.projection R ((names P)[i.val]'i.isLt)

theorem nonapplication_prefix (P : Presentation) (r : Fin (rows P).rowCount)
    (hr : ¬ applicationRow P r) : r.val<(rowsBefore P).length := by
  rw [applicationRow,rowList_length,Nat.add_sub_cancel_right,not_le] at hr
  exact hr

theorem actual_row_zero {P : Presentation} (R : StructuralRealization P) (r : Fin (rows P).rowCount)
    (hr : ¬ applicationRow P r) :
    ((rows P).constant r:ℂ) • (1:Op)+∑ i,((rows P).coefficient r i:ℂ) • numbered R i=0 := by
  rw [show (((rows P).constant r:ℂ) • (1:Op)+∑ i,((rows P).coefficient r i:ℂ) • numbered R i)=
      rowOperator (CompilerOrientedProjections.projection R) ((rowList P)[r.val]'r.isLt) from
        aggregate_row P (CompilerOrientedProjections.projection R) r]
  apply prefix_row_zero R
  have hlt := nonapplication_prefix P r hr
  have he : (rowList P)[r.val]?=some ((rowsBefore P)[r.val]'hlt) := by
    rw [rowList_append,List.getElem?_append_left hlt,List.getElem?_eq_getElem hlt]
  have ho : (rowList P)[r.val]?=some ((rowList P)[r.val]'r.isLt) := List.getElem?_eq_getElem r.isLt
  have hh := Option.some.inj (ho.symm.trans he)
  rw [hh]
  exact List.getElem_mem hlt

theorem rowOperator_transpose (N : ProjectionName → Op) (r : RationalRow) :
    rowOperator (fun n => transpose (N n)) r=transpose (rowOperator N r) := by
  have hs (xs : List Op) : transpose xs.sum=(xs.map transpose).sum := by
    induction xs with
    | nil => simp
    | cons A xs ih => simp only [List.sum_cons,List.map_cons,transpose_add,ih]
  simp only [rowOperator,transpose_add,transpose_smul,transpose_one,hs,List.map_map,Function.comp_def]

theorem transpose_sum {ι : Type} [Fintype ι] (F : ι → Op) :
    transpose (∑ i,F i)=∑ i,transpose (F i) := by
  let T : Op →ₗ[ℂ] Op := {
    toFun := transpose
    map_add' := transpose_add
    map_smul' := transpose_smul }
  exact map_sum T _ _

theorem actual_bob_row_zero {P : Presentation} (R : StructuralRealization P) (r : Fin (rows P).rowCount)
    (hr : ¬ applicationRow P r) :
    ((rows P).constant r:ℂ) • (1:Op)+∑ i,((rows P).coefficient r i:ℂ) • transpose (numbered R i)=0 := by
  have hh := congrArg transpose (actual_row_zero R r hr)
  simpa only [transpose_add,transpose_smul,transpose_one,transpose_sum,transpose_zero] using hh

/-- The exact compiler development RowsHoldOn record, with both genuine marginal densities. -/
theorem structuralRowsHold {P : Presentation} (R : StructuralRealization P) :
    StructuralRowsHold P (CompilerHonestRefinementsCorrect.strategy R) := by
  let A := CompilerHonestRefinementsCorrect.refinements R false
  let B := CompilerHonestRefinementsCorrect.refinements R true
  refine ⟨density R.density,transposedDensity (density R.density),?_,?_,?_,?_,?_⟩
  · exact CompilerHonestState.marginalA _ _
  · exact CompilerHonestState.marginalB _ _
  · intro i k hk
    exact named_mirror R A B i k
  · intro r hr
    change (((rows P).constant r:ℂ) • (1:Op)+∑ i : Fin (names P).length,
      ((rows P).coefficient r i:ℂ) • (CompilerHonestPregameBase.strategy R A B).measurements.alice
        (event P i).x (event P i).a)*(density R.density).op=0
    simp_rw [namedA]
    change (((rows P).constant r:ℂ) • (1:Op)+∑ i,((rows P).coefficient r i:ℂ) • numbered R i)*(density R.density).op=0
    rw [actual_row_zero R r hr,zero_mul]
  · intro r hr
    change (((rows P).constant r:ℂ) • (1:Op)+∑ i : Fin (names P).length,
      ((rows P).coefficient r i:ℂ) • (CompilerHonestPregameBase.strategy R A B).measurements.bob
        (event P i).y (event P i).b)*(transposedDensity (density R.density)).op=0
    simp_rw [namedB]
    change (((rows P).constant r:ℂ) • (1:Op)+∑ i,((rows P).coefficient r i:ℂ) • transpose (numbered R i))*
      (transposedDensity (density R.density)).op=0
    rw [actual_bob_row_zero R r hr,zero_mul]

/-- stage 6 base fields with the corrected stage 15 named projection dictionary. -/
theorem base15 (P : Presentation) (R : StructuralRealization P) :
    Perfect (preGame P) (CompilerHonestRefinementsCorrect.strategy R) ∧
    NamedBinaryProjections (rows P) (CompilerHonestRefinementsCorrect.strategy R) ∧
    StructuralRowsHold P (CompilerHonestRefinementsCorrect.strategy R) ∧
    MarginalA (CompilerHonestRefinementsCorrect.strategy R) (CompilerApproxDictionaryEnergy.oldDensity R) ∧
    (∀ i k,0<(CompilerHonestRefinementsCorrect.strategy R).weight k →
      left (numbered R i) ((CompilerHonestRefinementsCorrect.strategy R).vector k)=
        (CompilerHonestRefinementsCorrect.strategy R).measurements.left
          ((rows P).event i).x ((rows P).event i).a ((CompilerHonestRefinementsCorrect.strategy R).vector k)) := by
  refine ⟨CompilerHonestPregameCorrect.perfect R,
    CompilerHonestRefinementsCorrect.namedBinaryProjections R,structuralRowsHold R,
      CompilerHonestState.marginalA _ _,?_⟩
  intro i k hk
  rw [measurements_left]
  have he := namedA R (CompilerHonestRefinementsCorrect.refinements R false)
    (CompilerHonestRefinementsCorrect.refinements R true) ⟨i.val,i.isLt⟩
  exact congrArg (fun E : Op => left E ((CompilerHonestRefinementsCorrect.strategy R).vector k)) he.symm

#print axioms actual_row_zero
#print axioms actual_bob_row_zero
#print axioms structuralRowsHold
#print axioms base15
end Sigma2.CompilerHonestRows
