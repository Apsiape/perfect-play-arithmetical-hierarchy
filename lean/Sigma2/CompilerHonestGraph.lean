import Sigma2.CompilerHonestRowBlocks

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestRowAlgebra
open Compiler CompilerScaffold CompilerHonestQutrit CompilerProjectionDictionary
  CompilerHonestDictionary CompilerHonestLift CompilerHonestPairs FiniteAncilla
  CompilerApproxBlocks CompilerHonestPolynomial
open CompilerHonestRowBlocks
theorem frame_row {P : Presentation} (R : StructuralRealization P) :
    rowMatrix (blocks R) (row [(1,.frame 0),(1,.frame 1),(1,.frame 2)] (-1))=0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rowMatrix,row,blocks,singleBlocks,Matrix.one_apply] <;> module

theorem graph_rows {P : Presentation} (R : StructuralRealization P) (w : Word) (k : Fin 3)
    (r : RationalRow) (hr : r ∈ graphRows w k.val) : rowMatrix (blocks R) r=0 := by
  fin_cases k <;>
    simp only [graphRows,pairs,List.getElem?_cons_zero,List.getElem?_cons_succ,
      Option.getD_some,List.mem_cons,List.not_mem_nil,or_false] at hr
  all_goals rcases hr with rfl|rfl|rfl
  all_goals
    simp only [rowMatrix,row,blocks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    generalize evalWord (dictionary R) w=U
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rowMatrix,row,blocks,pairMatrix,pairPerm,graphMatrix,graphBlocks,
        calibratedBlocks,calibratedComplement,Equiv.swap_apply_def,singleBlocks,
        Matrix.add_apply,Matrix.smul_apply,star_neg]
  all_goals try rw [star_neg U]
  all_goals module

theorem triangle_row {P : Presentation} (R : StructuralRealization P) (u v w : Word)
    (hw : evalWord (dictionary R) w=evalWord (dictionary R) u*evalWord (dictionary R) v) :
    rowMatrix (blocks R) (triangleRow u v w)=0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [rowMatrix,row,triangleRow,blocks,pairMatrix,pairPerm,graphMatrix,
      graphBlocks,triangleBlocks,Equiv.swap_apply_def,singleBlocks,Matrix.one_apply,
      Matrix.add_apply,Matrix.smul_apply,hw]
  all_goals module


#print axioms graph_rows
#print axioms triangle_row
end Sigma2.CompilerHonestRowAlgebra
