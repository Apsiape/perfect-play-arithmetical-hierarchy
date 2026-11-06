import Sigma2.CompilerApproxDictionaryIndex

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxDictionaryEnergy
open Compiler CompilerScaffold CompilerApproxMatching CompilerApproxDictionaryIndex
  CompilerHonestDensity CompilerProjectionDictionary
attribute [local irreducible] names rowList words polynomials structuralPolynomials applicationPolynomials rowsBefore

def entryAt (P : Presentation) (R : StructuralRealization P) (j : Fin (applicationPolynomials P).length) :
    Entry := (entries P R)[j.val]'(by rw [entries_length]; exact j.isLt)

theorem entryAt_mem (P : Presentation) (R : StructuralRealization P) (j : Fin (applicationPolynomials P).length) :
    entryAt P R j∈entries P R := List.getElem_mem _

theorem entryAt_polynomial (P : Presentation) (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) :
    (entryAt P R j).1=(applicationPolynomials P)[j.val] := by
  have he := congrArg (fun xs : List Poly => xs[j.val]?) (entries_polynomials P R)
  have hv : j.val<(entries P R).length := by rw [entries_length]; exact j.isLt
  rw [List.getElem?_map,List.getElem?_eq_getElem hv,List.getElem?_eq_getElem j.isLt] at he
  exact Option.some.inj he

theorem residuals_length (P : Presentation) (R : StructuralRealization P) :
    (applicationResiduals P R).length=(applicationPolynomials P).length := by
  rw [← entries_residuals,List.length_map,entries_length]

def residualAt (P : Presentation) (R : StructuralRealization P) (j : Fin (applicationPolynomials P).length) : Op :=
  (entryAt P R j).2.2.2

theorem residualAt_get (P : Presentation) (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) :
    residualAt P R j=(applicationResiduals P R)[j.val]'(by rw [residuals_length]; exact j.isLt) := by
  have he := congrArg (fun xs : List Op => xs[j.val]?) (entries_residuals P R)
  have hv : j.val<(entries P R).length := by rw [entries_length]; exact j.isLt
  have hr : j.val<(applicationResiduals P R).length := by rw [residuals_length]; exact j.isLt
  rw [List.getElem?_map,List.getElem?_eq_getElem hv,List.getElem?_eq_getElem hr] at he
  exact Option.some.inj he

def beta (P : Presentation) (R : StructuralRealization P) (j : Fin (applicationPolynomials P).length) : ℝ :=
  121*(cornerWeight (entryAt P R j).2.2.1:ℝ)

theorem entry_input (P : Presentation) (R : StructuralRealization P) (t : Entry) (ht : t∈entries P R) :
    t.2.2.1=0 ∨ t.2.2.1=13 := by
  simp only [entries,List.mem_append,List.mem_flatMap,List.mem_map,List.mem_ofFn,
    List.mem_cons,List.not_mem_nil,or_false] at ht
  aesop

theorem beta_cases (P : Presentation) (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) : beta P R j=1 ∨ beta P R j=16 := by
  rcases entry_input P R _ (entryAt_mem P R j) with hs|hr
  · left; norm_num [beta,hs,cornerWeight]
  · right; norm_num [beta,hr,cornerWeight]

theorem beta_nonnegative (P : Presentation) (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) : 0≤beta P R j := by
  rcases beta_cases P R j with h|h <;> rw [h] <;> norm_num

theorem beta_le (P : Presentation) (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) : beta P R j≤16 := by
  rcases beta_cases P R j with h|h <;> rw [h] <;> norm_num

def oldDensity {P : Presentation} (R : StructuralRealization P) : Density :=
  weightedDensity 3 (fun _ => (1/3:ℝ)) (fun _ => by norm_num)
    (by norm_num [Fin.sum_univ_three]) (scaffoldDensity R.density)

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
  have he := CompilerHonestDictionaryAssembly.actual_polynomial_energy R ((applicationPolynomials P)[j.val])
  have ha := application_row_operator R j
  have hstar : star (CompilerHonestPolynomial.rowOperator (projection R)
      (polynomialRow ((applicationPolynomials P)[j.val])))=
    CompilerHonestPolynomial.rowOperator (projection R)
      (polynomialRow ((applicationPolynomials P)[j.val])) := by rw [← ha]; exact hA
  change (trace ((oldDensity R).op*(_*_))).re=_
  rw [ha]
  change (trace ((oldDensity R).op*(_*_))).re=_
  dsimp only at he
  rw [hstar] at he
  change (trace ((oldDensity R).op*(_*_))).re=_ at he
  rw [he,← entryAt_polynomial P R j,entry_energy P hP R _ (entryAt_mem P R j)]
  dsimp only [beta,residualAt]
  ring

#print axioms entryAt_polynomial
#print axioms residualAt_get
#print axioms beta_cases
#print axioms residual_matching
end Sigma2.CompilerApproxDictionaryEnergy
