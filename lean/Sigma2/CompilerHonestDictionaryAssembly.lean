import Sigma2.CompilerProjectionDictionary
import Sigma2.CompilerHonestFMSWeights
import Sigma2.CompilerHonestPolynomial

/-! stage 13 concrete honest dictionaries and measurement families.
This entry point does not assert the unfinished K4 or ApproxCompiled targets. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerHonestDictionaryAssembly
open Compiler CompilerScaffold CompilerHonestDictionary CompilerProjectionDictionary
  CompilerHonestPolynomial CompilerHonestDensity CompilerApproxQutrit FiniteAncilla

/-- The actual numbered projection dictionary interprets the literal frozen
polynomial row as exactly the qutrit lift of its evaluated polynomial. -/
theorem actual_polynomial_row {P : Presentation} (R : StructuralRealization P) (p : Poly) :
    rowOperator (projection R) (polynomialRow p)=
      matrixOp 3 (residualBlocks (evalPoly (dictionary R) p)) := by
  calc
    _=rowOperator (polynomialName (dictionary R)) (polynomialRow p) := by
      simp only [rowOperator,polynomialRow,row,List.map_append,List.map_map,Function.comp_def,
        List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil]
      simp_rw [projection_graph_zero]
      rfl
    _=matrixOp 3 (residualBlocks (evalPoly (dictionary R) p)) := by
      rw [polynomialRow_operator,rowBlocks_eq]

/-- The exact 2/3 energy factor holds for the actual frozen polynomial rows
of the simultaneous honest dictionary, with their actual projection values. -/
theorem actual_polynomial_energy {P : Presentation} (R : StructuralRealization P) (p : Poly) :
    let h := scaffoldDensity R.density
    let qh := weightedDensity 3 (fun _ => (1/3:ℝ)) (fun _ => by norm_num)
      (by norm_num [Fin.sum_univ_three]) h
    let A := rowOperator (projection R) (polynomialRow p)
    (trace (qh.op*(star A*A))).re=
      (2/3:ℝ)*(trace (h.op*(star (evalPoly (dictionary R) p)*evalPoly (dictionary R) p))).re := by
  dsimp only
  rw [actual_polynomial_row]
  exact qutrit_residual_energy _ _
    (evalPoly_centralizer _ _ (dictionary_centralizer R) p)

#print axioms actual_polynomial_row
#print axioms actual_polynomial_energy
end Sigma2.CompilerHonestDictionaryAssembly
