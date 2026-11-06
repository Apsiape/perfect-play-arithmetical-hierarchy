import Sigma2.CompilerApproxIndex
import Sigma2.CompilerApproxDictionaryEnergy
import Sigma2.CompilerHonestPolynomialCorrect
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerApproxEnergy
open Compiler CompilerScaffold CompilerApproxMatching CompilerApproxDictionaryEnergy CompilerApproxIndex
  CompilerOrientedProjections
/-- The literal numbered row, with the same application index as the original
residual list, has exactly the scaffold/qutrit residual energy. -/
theorem residual_matching (P : Presentation) (hP : P.admissible) (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) :
    let A := CompilerEventSlots.rowOperator (rows P) (numbered R) (rowIndex P j)
    (trace ((oldDensity R).op*(A*A))).re=
      (2*beta P R j/363)*(trace (R.density.op*(star (residualAt P R j)*residualAt P R j))).re := by
  dsimp only
  have hA := CompilerEventSlots.rowOperator_selfadjoint (rows P) (numbered R)
    (numbered_projection R) (rowIndex P j)
  have he := CompilerHonestPolynomialCorrect.polynomialRow_energy R ((applicationPolynomials P)[j.val])
  have ha := application_row_operator R j
  have hstar : star (CompilerHonestPolynomial.rowOperator (projection R)
      (polynomialRow ((applicationPolynomials P)[j.val])))=
    CompilerHonestPolynomial.rowOperator (projection R)
      (polynomialRow ((applicationPolynomials P)[j.val])) := by rw [← ha]; exact hA
  change (trace ((oldDensity R).op*(_*_))).re=_
  rw [ha]
  change (trace ((oldDensity R).op*(_*_))).re=_
  rw [hstar] at he
  change (trace ((oldDensity R).op*(_*_))).re=_ at he
  rw [he,← entryAt_polynomial P R j,entry_energy P hP R _ (entryAt_mem P R j)]
  dsimp only [beta,residualAt]
  ring

#print axioms entryAt_polynomial
#print axioms residualAt_get
#print axioms beta_cases
#print axioms residual_matching
end Sigma2.CompilerApproxEnergy
