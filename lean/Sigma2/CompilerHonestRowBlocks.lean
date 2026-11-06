import Sigma2.CompilerHonestStrategy

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestRowBlocks
open Compiler CompilerScaffold CompilerHonestQutrit CompilerProjectionDictionary
  CompilerHonestDictionary CompilerHonestLift CompilerHonestPairs FiniteAncilla
  CompilerApproxBlocks CompilerHonestPolynomial
abbrev M := Matrix (Fin 3) (Fin 3) Op

def pairMatrix (k : ℕ) (A : M) : M :=
  if k=2 then fun i j => A (pairPerm 2 (pairPerm 2 i)) (pairPerm 2 (pairPerm 2 j))
  else fun i j => A (pairPerm k i) (pairPerm k j)

def graphMatrix (U : Op) (part : ℕ) : M :=
  if part=0 then graphBlocks U else if part=1 then graphBlocks (-U)
  else if part=2 then calibratedBlocks U else calibratedComplement U

theorem graphPart_matrix (U : Op) (part : ℕ) : graphPart U part=matrixOp 3 (graphMatrix U part) := by
  unfold graphPart graphMatrix
  split_ifs <;> rfl

def blocks {P : Presentation} (R : StructuralRealization P) : ProjectionName → M
  | .parameter p => Matrix.diagonal (fun _ => parameter p)
  | .active g => Matrix.diagonal (fun _ => CompilerFiniteRegister.mask 17 (bridgeActive g))
  | .frame i => singleBlocks 3 ⟨i%3,Nat.mod_lt _ (by norm_num)⟩ ⟨i%3,Nat.mod_lt _ (by norm_num)⟩ 1
  | .graph w k part => pairMatrix k (graphMatrix (evalWord (dictionary R) w) part)
  | .triangle u v _ => triangleBlocks (evalWord (dictionary R) u) (evalWord (dictionary R) v)
      (evalWord (dictionary R) u*evalWord (dictionary R) v)
  | .binding p i c => singleBlocks 3 ⟨i%3,Nat.mod_lt _ (by norm_num)⟩ ⟨i%3,Nat.mod_lt _ (by norm_num)⟩
      (if c then 1-parameter p else parameter p)
  | .joint p k a b => pairMatrix k (jointBlocks (if a=1 then parameter p else 1-parameter p) (decide (b=1)))

theorem projection_blocks {P : Presentation} (R : StructuralRealization P) (n : ProjectionName) :
    CompilerOrientedProjections.projection R n=matrixOp 3 (blocks R n) := by
  cases n with
  | parameter p => exact (RowCompleteness.matrixOp_constantDiagonal 3 _).symm
  | active g => exact (RowCompleteness.matrixOp_constantDiagonal 3 _).symm
  | frame i => rfl
  | triangle u v w => rfl
  | binding p i c => rfl
  | graph w k part =>
      simp only [CompilerOrientedProjections.projection,CompilerOrientedProjections.repair,
        CompilerProjectionDictionary.projection,blocks,graphPart_matrix]
      by_cases hk : k=2
      · subst k
        simp [inPair_matrix,pairMatrix,graphMatrix]
      · simp [hk,inPair_matrix,pairMatrix,graphMatrix]
  | joint p k a b =>
      simp only [CompilerOrientedProjections.projection,CompilerOrientedProjections.repair,
        CompilerProjectionDictionary.projection,blocks]
      by_cases hk : k=2
      · subst k
        simp [inPair_matrix,pairMatrix]
      · simp [hk,inPair_matrix,pairMatrix]

def rowMatrix (N : ProjectionName → M) (r : RationalRow) : M :=
  (r.constant:ℂ) • 1+(r.terms.map (fun t => (t.1:ℂ) • N t.2)).sum

theorem rowOperator_blocks {P : Presentation} (R : StructuralRealization P) (r : RationalRow) :
    rowOperator (CompilerOrientedProjections.projection R) r=matrixOp 3 (rowMatrix (blocks R) r) := by
  simp only [rowOperator,rowMatrix,matrixOp_add,matrixOp_smul,matrixOp_one,
    matrixOp_list_sum,List.map_map,Function.comp_def,projection_blocks]


#print axioms projection_blocks
end Sigma2.CompilerHonestRowBlocks
