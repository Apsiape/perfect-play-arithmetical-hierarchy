import Sigma2.CompilerHonestGraph

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestRowAlgebra
open Compiler CompilerScaffold CompilerHonestQutrit CompilerProjectionDictionary
  CompilerHonestDictionary CompilerHonestLift CompilerHonestPairs FiniteAncilla
  CompilerApproxBlocks CompilerHonestPolynomial
open CompilerHonestRowBlocks
theorem binding_rows {P : Presentation} (R : StructuralRealization P) (p : ℕ) (hp : p<25)
    (r : RationalRow) (hr : r ∈ bindingRows p) : rowMatrix (blocks R) r=0 := by
  have hw : evalWord (dictionary R) [(p,false)]=reflection (parameter p) := by
    simp [evalWord,dictionary,hp]
  have hs : star ((2:ℂ) • parameter p-1)=(2:ℂ) • parameter p-1 := by
    rw [star_sub ((2:ℂ) • parameter p) (1:Op),star_smul (2:ℂ) (parameter p),(parameter_projection p).1,star_one]
    norm_num
  simp only [bindingRows,List.mem_append,List.mem_map,List.mem_range,List.mem_cons,
    List.not_mem_nil,or_false,List.mem_flatMap] at hr
  rcases hr with (hr|hr)|hr
  · obtain ⟨i,hi,rfl⟩ := hr
    interval_cases i <;> apply Matrix.ext <;> intro a b <;> fin_cases a <;> fin_cases b <;>
      norm_num [rowMatrix,row,blocks,singleBlocks] <;> module
  · rcases hr with rfl|rfl
    all_goals
      simp only [rowMatrix,row,blocks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hw,
        show evalWord (dictionary R) []=1 by rfl]
      apply Matrix.ext
      intro a b
      fin_cases a <;> fin_cases b <;>
      norm_num [rowMatrix,row,blocks,singleBlocks,List.range_succ,Matrix.diagonal_apply,
        Matrix.one_apply] <;> module
  · obtain ⟨k,hk,hr⟩ := hr
    interval_cases k <;>
      simp only [pairs,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
        List.mem_cons,List.not_mem_nil,or_false] at hr
    all_goals rcases hr with rfl|rfl|rfl|rfl
    all_goals
      simp only [rowMatrix,row,blocks,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hw,
        show evalWord (dictionary R) []=1 by rfl]
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        norm_num [rowMatrix,row,blocks,pairMatrix,pairPerm,graphMatrix,graphBlocks,
          jointBlocks,Equiv.swap_apply_def,singleBlocks,hs,
          CompilerHonestDictionary.reflection,star_sub,star_smul,star_one,
          (parameter_projection p).1,Matrix.add_apply,Matrix.smul_apply]
    all_goals try simp only [hw,show evalWord (dictionary R) []=1 by rfl,
      CompilerHonestDictionary.reflection,hs]
    all_goals module

#print axioms projection_blocks
#print axioms graph_rows
#print axioms triangle_row
#print axioms binding_rows
end Sigma2.CompilerHonestRowAlgebra
