import Sigma2.CompilerHonestRowAlgebra
import Sigma2.CompilerHonestStructural

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestListRows
open Compiler CompilerScaffold CompilerHonestDictionary CompilerFiniteRegister
  CompilerHonestLift CompilerHonestSyntax CompilerApproxDictionary
  CompilerApproxResidual CompilerRegisterIdentities CompilerHonestStructural FiniteAncilla
  CompilerHonestRowBlocks CompilerHonestRowAlgebra CompilerHonestPolynomial
  CompilerApproxDictionaryIndex
attribute [local irreducible] names rowList words polynomials structuralPolynomials applicationPolynomials rowsBefore

theorem token_inverse {P : Presentation} (R : StructuralRealization P) (t : Token) :
    evalWord (dictionary R) [t]*evalWord (dictionary R) [(t.1,!t.2)]=1 := by
  rcases t with ⟨n,b⟩
  cases b <;> simp [evalWord,(dictionary_unitary R n).1,(dictionary_unitary R n).2]

theorem word_rows {P : Presentation} (R : StructuralRealization P) (w : Word)
    (r : RationalRow) (hr : r ∈ wordRows w) : rowMatrix (blocks R) r=0 := by
  simp only [wordRows,List.mem_append,List.mem_flatMap,List.mem_range,List.mem_cons,
    List.not_mem_nil,or_false] at hr
  rcases hr with ((hr|hr)|hr)|hr
  · obtain ⟨k,hk,hr⟩ := hr
    exact graph_rows R w ⟨k,hk⟩ r hr
  · rcases hr with rfl|rfl
    · exact triangle_row R w [] w (by simp [evalWord])
    · exact triangle_row R [] w w (by simp [evalWord])
  · split_ifs at hr with h
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      subst r
      apply triangle_row
      rw [← evalWord_append,List.take_append_drop]
    · contradiction
  · cases w with
    | nil => simp at hr
    | cons t ts =>
      cases ts with
      | nil =>
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl|rfl
        · exact triangle_row R [t] [(t.1,!t.2)] [] (token_inverse R t).symm
        · apply triangle_row
          simpa only [evalWord,Bool.not_not] using (token_inverse R (t.1,!t.2)).symm
      | cons s ss => simp at hr

theorem activity_row {P : Presentation} (R : StructuralRealization P) (g : Fin 4) :
    rowMatrix (blocks R) (row ([(1,.active g.val),(-1,.parameter (cornerIndex g.val))] ++
      (List.range 4).map (fun k => (-1,.parameter (1+4*g.val+k)))))=0 := by
  have hs : parameter (cornerIndex g.val)=CompilerFiniteRegister.corner 17 (selected g.val) := by
    have he := eval_e R g.val (by have := g.isLt; omega)
    rw [e,eval_parameter R _ (by dsimp [cornerIndex]; split_ifs <;> have := g.isLt <;> omega)] at he
    exact he
  have hm : (∑ k : Fin 4,parameter (1+4*g.val+k.val))=mask 17 (magicActive g) := by
    rw [← magic_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [parameter,dif_pos (show 1+4*g.val+k.val<17 by have := g.isLt; have := k.isLt; omega)]
    rfl
  have ha := (activity_sum g).symm
  rw [← hs,← hm] at ha
  norm_num [Fin.sum_univ_succ] at ha
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rowMatrix,row,blocks,List.range_succ,Matrix.diagonal_apply,Matrix.one_apply]
  all_goals try rw [ha]
  all_goals module

/-- Every row before the application suffix is an exact global operator identity. -/
theorem prefix_row_zero {P : Presentation} (R : StructuralRealization P)
    (r : RationalRow) (hr : r ∈ rowsBefore P) :
    rowOperator (CompilerOrientedProjections.projection R) r=0 := by
  simp only [rowsBefore,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    List.mem_flatMap,List.mem_map,List.mem_range] at hr
  rcases hr with (((hr|hr)|hr)|hr)|hr
  · rcases hr with rfl|rfl
    · rw [rowOperator_blocks,frame_row,matrixOp_zero]
    · rw [rowOperator_blocks,triangle_row R [] [] [] (by simp [evalWord]),matrixOp_zero]
  · obtain ⟨p,hp,hr⟩ := hr
    rw [rowOperator_blocks,binding_rows R p hp r hr,matrixOp_zero]
  · obtain ⟨w,hw,hr⟩ := hr
    rw [rowOperator_blocks,word_rows R w r hr,matrixOp_zero]
  · obtain ⟨g,hg,rfl⟩ := hr
    rw [rowOperator_blocks,activity_row R ⟨g,hg⟩,matrixOp_zero]
  · obtain ⟨p,hp,rfl⟩ := hr
    exact CompilerHonestPolynomialCorrect.polynomialRow_zero R p (structural_zero R p hp)

/-- Coalescing repeated names preserves every literal row, including its constant. -/
theorem aggregate_row (P : Presentation) (N : ProjectionName → Op) (r : Fin (rows P).rowCount) :
    ((rows P).constant r:ℂ) • (1:Op)+∑ i : Fin (rows P).count,
      ((rows P).coefficient r i:ℂ) • N ((names P)[i.val]'i.isLt)=
        rowOperator N ((rowList P)[r.val]'r.isLt) := by
  change (_:ℂ) • (1:Op)+∑ i : Fin (names P).length,
    (coefficient ((rowList P)[r.val]'r.isLt) ((names P)[i.val]'i.isLt):ℂ) • N ((names P)[i.val]'i.isLt)=_
  unfold rowOperator coefficient
  congr 1
  apply aggregate (names P) (names_nodup P) N ((rowList P)[r.val]'r.isLt).terms
  intro t ht
  exact row_name_mem P _ (List.getElem_mem r.isLt) t.2 (List.mem_map.mpr ⟨t,ht,rfl⟩)

#print axioms word_rows
#print axioms activity_row
#print axioms prefix_row_zero
#print axioms aggregate_row
end Sigma2.CompilerHonestListRows
