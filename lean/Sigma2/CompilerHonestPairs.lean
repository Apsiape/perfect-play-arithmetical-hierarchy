import Sigma2.CompilerHonestMeasurements

/-! Explicit pair-convention audit and a new corrected permutation. Existing
 dictionary modules remain frozen. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestPairs
open Compiler CompilerScaffold CompilerProjectionDictionary CompilerFiniteRegister
  CompilerHonestQutrit CompilerHonestLift CompilerHonestScalar
  CompilerHonestPolynomial FiniteAncilla RowCompleteness

theorem inPair_matrix (k : ℕ) (A : Matrix (Fin 3) (Fin 3) Op) :
    inPair k (matrixOp 3 A)=matrixOp 3 (fun i j => A (pairPerm k i) (pairPerm k j)) := by
  rw [inPair,permutation,← matrixOp_star,permutation_star,← matrixOp_mul,← matrixOp_mul]
  congr 1
  apply Matrix.ext
  intro i j
  rw [permutation_right,permutation_left]
  simp

 theorem old_pair_two_frame :
    inPair 2 (matrixOp 3 pairFrame)=frame 0+frame 2 := by
  rw [inPair_matrix]
  change matrixOp 3 _=matrixOp 3 (CompilerApproxBlocks.singleBlocks 3 0 0 1)+
    matrixOp 3 (CompilerApproxBlocks.singleBlocks 3 2 2 1)
  rw [← matrixOp_add]
  congr 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairPerm,pairFrame,Equiv.swap_apply_def,CompilerApproxBlocks.singleBlocks]

theorem graph_sum (U : Op) : graphBlocks U+graphBlocks (-U)=pairFrame := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [graphBlocks,pairFrame,star_neg,Matrix.add_apply]
  all_goals try rw [star_neg U]
  all_goals module

theorem inPair_add (k : ℕ) (A B : Op) : inPair k (A+B)=inPair k A+inPair k B := by
  simp [inPair,mul_add,add_mul]

/-- The old dictionary's k=2 graph pair sums to frames 0 and 2, although the
 frozen graph row at k=2 subtracts frames 1 and 2. -/
theorem old_graph_two_sum {P : Presentation} (R : StructuralRealization P) (w : Word) :
    projection R (.graph w 2 0)+projection R (.graph w 2 1)=frame 0+frame 2 := by
  change inPair 2 (matrixOp 3 (graphBlocks _))+inPair 2 (matrixOp 3 (graphBlocks (-_)))=_
  rw [← inPair_add,← matrixOp_add,graph_sum,old_pair_two_frame]

def pairPerm15 (k : ℕ) : Equiv.Perm (Fin 3) :=
  if k=2 then Equiv.swap 1 2*Equiv.swap 0 1 else pairPerm k

def inPair15 (k : ℕ) (A : Op) : Op :=
  permutation 3 (pairPerm15 k)*A*star (permutation 3 (pairPerm15 k))

theorem corrected_pair_two_frame :
    inPair15 2 (matrixOp 3 pairFrame)=frame 1+frame 2 := by
  rw [inPair15,permutation,← matrixOp_star,permutation_star,← matrixOp_mul,← matrixOp_mul]
  change matrixOp 3 _=matrixOp 3 (CompilerApproxBlocks.singleBlocks 3 1 1 1)+
    matrixOp 3 (CompilerApproxBlocks.singleBlocks 3 2 2 1)
  rw [← matrixOp_add]
  congr 1
  apply Matrix.ext
  intro i j
  rw [permutation_right,permutation_left]
  fin_cases i <;> fin_cases j <;>
    norm_num [pairPerm15,pairFrame,Equiv.swap_apply_def,CompilerApproxBlocks.singleBlocks]

#print axioms old_graph_two_sum
#print axioms corrected_pair_two_frame
end Sigma2.CompilerHonestPairs
