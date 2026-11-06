import Sigma2.CompilerOrientedProjections

/-! Literal polynomial rows evaluated in the actual simultaneous CompilerOrientedProjections.projection
 dictionary, retaining their qutrit residual and exact energy factor. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestPolynomialCorrect
open Compiler CompilerScaffold CompilerHonestPolynomial CompilerProjectionDictionary
  CompilerHonestDictionary CompilerHonestQutrit CompilerHonestDensity
  CompilerHonestFMSLift FiniteAncilla

 theorem frame_zero {P : Presentation} (R : StructuralRealization P) :
    CompilerOrientedProjections.projection R (.frame 0)=polynomialName (dictionary R) (.frame 0) := rfl
 theorem frame_one {P : Presentation} (R : StructuralRealization P) :
    CompilerOrientedProjections.projection R (.frame 1)=polynomialName (dictionary R) (.frame 1) := rfl

/-- The frozen list row uses the actual values of the simultaneous dictionary. -/
theorem polynomialRow_operator {P : Presentation} (R : StructuralRealization P) (p : Poly) :
    rowOperator (CompilerOrientedProjections.projection R) (polynomialRow p)=matrixOp 3 (rowBlocks (dictionary R) p) := by
  rw [← CompilerHonestPolynomial.polynomialRow_operator]
  simp only [rowOperator,polynomialRow,row,List.map_append,List.map_map,Function.comp_def,
    List.map_cons,List.map_nil,CompilerOrientedProjections.projection_graph_zero,frame_zero,frame_one,polynomialName]

 theorem polynomialRow_zero {P : Presentation} (R : StructuralRealization P) (p : Poly)
    (hz : evalPoly (dictionary R) p=0) : rowOperator (CompilerOrientedProjections.projection R) (polynomialRow p)=0 := by
  rw [polynomialRow_operator,rowBlocks_eq,hz,residual_zero,matrixOp_zero]

/-- The same polynomial-row operator on the genuine qutrit/scaffold marginal
 has exactly the required 2/3 energy factor. -/
theorem polynomialRow_energy {P : Presentation} (R : StructuralRealization P) (p : Poly) :
    (trace ((density R.density).op*
      (star (rowOperator (CompilerOrientedProjections.projection R) (polynomialRow p))*rowOperator (CompilerOrientedProjections.projection R) (polynomialRow p)))).re=
      (2/3:ℝ)*(trace ((scaffoldDensity R.density).op*
        (star (evalPoly (dictionary R) p)*evalPoly (dictionary R) p))).re := by
  rw [polynomialRow_operator]
  exact row_energy (scaffoldDensity R.density) (dictionary R) (dictionary_centralizer R) p

#print axioms polynomialRow_operator
#print axioms polynomialRow_zero
#print axioms polynomialRow_energy
end Sigma2.CompilerHonestPolynomialCorrect
