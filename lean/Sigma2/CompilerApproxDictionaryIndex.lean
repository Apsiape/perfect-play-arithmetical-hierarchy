import Sigma2.CompilerApproxMatching
import Sigma2.CompilerEventLoss

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxDictionaryIndex
open Compiler CompilerScaffold CompilerEventLoss CompilerApproxMatching
  CompilerProjectionDictionary
attribute [local irreducible] names rowList words polynomials structuralPolynomials applicationPolynomials

 def rowsBefore (P : Presentation) : List RationalRow :=
  [row [(1,.frame 0),(1,.frame 1),(1,.frame 2)] (-1),triangleRow [] [] []] ++
  (List.range 25).flatMap bindingRows ++ (words P).flatMap wordRows ++
  (List.range 4).map (fun g => row ([(1,.active g),(-1,.parameter (cornerIndex g))] ++
    (List.range 4).map (fun k => (-1,.parameter (1+4*g+k))))) ++
  (structuralPolynomials P).map polynomialRow

attribute [local irreducible] rowsBefore

 theorem rowList_append (P : Presentation) :
    rowList P=rowsBefore P++(applicationPolynomials P).map polynomialRow := by
  simp only [rowList,rowsBefore,polynomials,List.map_append,List.append_assoc]

 theorem rowList_length (P : Presentation) :
    (rowList P).length=(rowsBefore P).length+(applicationPolynomials P).length := by
  rw [rowList_append,List.length_append,List.length_map]

 def rowIndex (P : Presentation) (j : Fin (applicationPolynomials P).length) : Fin (rows P).rowCount :=
  ⟨(rowsBefore P).length+j.val,by change _<(rowList P).length; rw [rowList_length]; omega⟩

 theorem rowIndex_application (P : Presentation) (j : Fin (applicationPolynomials P).length) :
    applicationRow P (rowIndex P j) := by
  unfold applicationRow rowIndex
  rw [rowList_length,Nat.add_sub_cancel_right]
  change (rowsBefore P).length≤(rowsBefore P).length+j.val
  omega

 theorem application_index (P : Presentation) (r : Fin (rows P).rowCount)
    (hr : applicationRow P r) : ∃ j,rowIndex P j=r := by
  have hl := rowList_length P
  have hrlt : r.val<(rowList P).length := r.isLt
  have hp : (rowsBefore P).length≤r.val := by
    simpa only [applicationRow,hl,Nat.add_sub_cancel_right] using hr
  refine ⟨⟨r.val-(rowsBefore P).length,by omega⟩,?_⟩
  apply Fin.ext
  dsimp [rowIndex]
  omega

 theorem rowIndex_get (P : Presentation) (j : Fin (applicationPolynomials P).length) :
    ((rowList P)[(rowIndex P j).val]'(rowIndex P j).isLt)=polynomialRow ((applicationPolynomials P)[j.val]) := by
  have hv : (rowsBefore P).length+j.val<(rowList P).length := by
    rw [rowList_length]; omega
  have ho : (rowList P)[(rowsBefore P).length+j.val]?=
      some (polynomialRow ((applicationPolynomials P)[j.val])) := by
    rw [rowList_append,List.getElem?_append_right (show (rowsBefore P).length≤(rowsBefore P).length+j.val by omega),
      Nat.add_sub_cancel_left,List.getElem?_map,List.getElem?_eq_getElem j.isLt]
    rfl
  have hg := List.getElem?_eq_getElem hv
  exact Option.some.inj (hg.symm.trans ho)

 def numbered {P : Presentation} (R : StructuralRealization P) (i : Fin (rows P).count) : Op :=
  projection R (((names P)[i.val]'i.isLt))

 theorem numbered_projection {P : Presentation} (R : StructuralRealization P) :
    ∀ i,Projection (numbered R i) := fun i => projection_projective R _

 theorem aggregate (ns : List ProjectionName) (hn : ns.Nodup) (N : ProjectionName → Op)
    (xs : List (ℚ × ProjectionName)) (hx : ∀ t∈xs,t.2∈ns) :
    (∑ i : Fin ns.length,((((xs.filter (fun t => t.2=ns[i.val])).map Prod.fst).sum:ℚ):ℂ) • N ns[i.val])=
      (xs.map (fun t => (t.1:ℂ) • N t.2)).sum := by
  classical
  let c : List (ℚ × ProjectionName) → ProjectionName → ℚ :=
    fun ys n => ((ys.filter (fun u => u.2=n)).map Prod.fst).sum
  change (∑ i : Fin ns.length,(c xs ns[i.val]:ℂ) • N ns[i.val])=_
  induction xs with
  | nil =>
      simp only [c,List.filter_nil,List.map_nil,List.sum_nil,Rat.cast_zero]
      apply Finset.sum_eq_zero
      intro i hi
      module
  | cons t xs ih =>
      have hmem : t.2∈ns := hx t (by simp)
      let k : Fin ns.length := ⟨ns.idxOf t.2,List.idxOf_lt_length_of_mem hmem⟩
      have hk : ns[k.val]=t.2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hmem)
      have he (i : Fin ns.length) : t.2=ns[i.val] ↔ i=k := by
        constructor
        · intro hi
          exact hn.injective_get (hi.symm.trans hk.symm)
        · intro hi; subst i; exact hk.symm
      have hs (i : Fin ns.length) :
          (c (t::xs) ns[i.val]:ℂ) • N ns[i.val]=
          (if t.2=ns[i.val] then (t.1:ℂ) • N ns[i.val] else 0)+
          (c xs ns[i.val]:ℂ) • N ns[i.val] := by
        by_cases ht : t.2=ns[i.val] <;>
          simp [c,List.filter_cons,ht,Rat.cast_add,add_smul,zero_smul] <;> module
      simp_rw [hs]
      rw [Finset.sum_add_distrib,ih (fun u hu => hx u (by simp [hu]))]
      simp only [List.map_cons,List.sum_cons]
      congr 1
      simp only [he]
      simp [hk]

 theorem numbered_row {P : Presentation} (R : StructuralRealization P) (r : Fin (rows P).rowCount) :
    CompilerEventSlots.rowOperator (rows P) (numbered R) r=
    CompilerHonestPolynomial.rowOperator (projection R) (((rowList P)[r.val]'r.isLt)) := by
  change (_:ℂ) • (1:Op)+∑ i : Fin (names P).length,
    (coefficient (((rowList P)[r.val]'r.isLt)) (((names P)[i.val]'i.isLt)):ℂ) • projection R (((names P)[i.val]'i.isLt))=_
  unfold CompilerHonestPolynomial.rowOperator coefficient
  congr 1
  apply aggregate (names P) (names_nodup P) (projection R) (((rowList P)[r.val]'r.isLt)).terms
  intro t ht
  exact row_name_mem P _ (List.getElem_mem r.isLt) t.2 (List.mem_map.mpr ⟨t,ht,rfl⟩)

 theorem application_row_operator {P : Presentation} (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) :
    CompilerEventSlots.rowOperator (rows P) (numbered R) (rowIndex P j)=
    CompilerHonestPolynomial.rowOperator (projection R)
      (polynomialRow ((applicationPolynomials P)[j.val])) := by
  rw [numbered_row,rowIndex_get]

#print axioms rowIndex_application
#print axioms application_index
#print axioms rowIndex_get
#print axioms numbered_row
#print axioms application_row_operator
end Sigma2.CompilerApproxDictionaryIndex
