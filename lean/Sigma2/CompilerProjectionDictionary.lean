import Sigma2.CompilerHonestDictionary

/-! A simultaneous projection dictionary for every frozen ProjectionName.
Graph pairs are scalar qutrit conjugates of the same word dictionary, and
triangle witnesses use its actual products. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerProjectionDictionary
open Compiler CompilerScaffold CompilerHonestQutrit CompilerHonestLift
  CompilerFiniteRegister FiniteAncilla
abbrev M := Matrix (Fin 3) (Fin 3) Op

theorem conjugate_projection (U P : Op) (hU : Unitary U) (hP : Projection P) :
    Projection (U*P*star U) := by
  constructor
  · rw [star_mul,star_mul,star_star,hP.1]
    exact mul_assoc _ _ _
  · calc
      (U*P*star U)*(U*P*star U)=U*P*(star U*U)*P*star U := by noncomm_ring
      _=U*P*star U := by rw [hU.1,mul_one,mul_assoc U P P,hP.2]

theorem amplify_projection (P : Op) (hP : Projection P) : Projection (amplify 3 P) := by
  constructor
  · rw [← amplify_star,hP.1]
  · rw [← amplify_mul,hP.2]

theorem lift_projection (i : Fin 3) (P : Op) (hP : Projection P) : Projection (lift 3 i i P) := by
  constructor
  · rw [lift_star,hP.1]
  · rw [lift_mul,if_pos rfl,hP.2]

def pairPerm (k : ℕ) : Equiv.Perm (Fin 3) :=
  if k=0 then 1 else if k=1 then Equiv.swap 1 2 else Equiv.swap 0 1*Equiv.swap 1 2

def inPair (k : ℕ) (P : Op) : Op :=
  permutation 3 (pairPerm k)*P*star (permutation 3 (pairPerm k))

theorem inPair_projection (k : ℕ) (P : Op) (hP : Projection P) : Projection (inPair k P) :=
  conjugate_projection _ _ (permutation_unitary 3 _) hP

theorem neg_unitary (U : Op) (hU : Unitary U) : Unitary (-U) := by
  constructor
  · rw [star_neg U,neg_mul_neg (star U) U]; exact hU.1
  · rw [star_neg U,neg_mul_neg U (star U)]; exact hU.2

/-- The complement of the calibrated 3-4-5 graph in its two-corner frame. -/
def calibratedComplement (U : Op) : M :=
  !![(1/5:ℂ) • (1:Op),(-2/5:ℂ) • U,0;
     (-2/5:ℂ) • star U,(4/5:ℂ) • (1:Op),0;
     0,0,0]

theorem calibratedComplement_projection (U : Op) (hU : Unitary U) :
    Projection (matrixOp 3 (calibratedComplement U)) := by
  apply matrixOp_projection
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [calibratedComplement,Matrix.star_apply,star_zero Op]
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [calibratedComplement,Matrix.mul_apply,Fin.sum_univ_three,
        smul_mul_smul_comm,hU.1,hU.2] <;> module

def graphPart (U : Op) (part : ℕ) : Op :=
  if part=0 then matrixOp 3 (graphBlocks U)
  else if part=1 then matrixOp 3 (graphBlocks (-U))
  else if part=2 then matrixOp 3 (calibratedBlocks U)
  else matrixOp 3 (calibratedComplement U)

theorem graphPart_projection (U : Op) (hU : Unitary U) (part : ℕ) :
    Projection (graphPart U part) := by
  dsimp only [graphPart]
  split_ifs
  · exact graph_projection U hU
  · exact graph_projection (-U) (neg_unitary U hU)
  · exact calibrated_projection U hU
  · exact calibratedComplement_projection U hU

/-- A common scalar graph, restricted to one separate binary label outcome. -/
def jointBlocks (P : Op) (positive : Bool) : M :=
  let s : ℂ := if positive then 1/2 else -1/2
  !![(1/2:ℂ) • P,s • P,0;s • P,(1/2:ℂ) • P,0;0,0,0]

theorem joint_projection (P : Op) (hP : Projection P) (positive : Bool) :
    Projection (matrixOp 3 (jointBlocks P positive)) := by
  apply matrixOp_projection
  · apply Matrix.ext
    intro i j
    cases positive <;> fin_cases i <;> fin_cases j <;>
      simp [jointBlocks,Matrix.star_apply,star_smul,hP.1,star_zero Op]
  · apply Matrix.ext
    intro i j
    cases positive <;> fin_cases i <;> fin_cases j <;>
      norm_num [jointBlocks,Matrix.mul_apply,Fin.sum_univ_three,
        smul_mul_smul_comm,hP.2] <;> module

def frame (i : ℕ) : Op := lift 3 ⟨i%3,Nat.mod_lt _ (by norm_num)⟩ ⟨i%3,Nat.mod_lt _ (by norm_num)⟩ 1

/-- All frozen names now have one simultaneous honest projection value. -/
def projection {P : Presentation} (R : StructuralRealization P) : ProjectionName → Op
  | .parameter i => amplify 3 (CompilerHonestDictionary.parameter i)
  | .active g => amplify 3 (mask 17 (CompilerHonestDictionary.bridgeActive g))
  | .frame i => frame i
  | .graph w k part => inPair k (graphPart (evalWord (CompilerHonestDictionary.dictionary R) w) part)
  | .triangle u v _ => matrixOp 3 (triangleBlocks
      (evalWord (CompilerHonestDictionary.dictionary R) u)
      (evalWord (CompilerHonestDictionary.dictionary R) v)
      (evalWord (CompilerHonestDictionary.dictionary R) u*
        evalWord (CompilerHonestDictionary.dictionary R) v))
  | .binding p i complement => lift 3 ⟨i%3,Nat.mod_lt _ (by norm_num)⟩ ⟨i%3,Nat.mod_lt _ (by norm_num)⟩
      (if complement then 1-CompilerHonestDictionary.parameter p else CompilerHonestDictionary.parameter p)
  | .joint p pair a b => inPair pair (matrixOp 3 (jointBlocks
      (if a=1 then CompilerHonestDictionary.parameter p else 1-CompilerHonestDictionary.parameter p)
      (decide (b=1))))

theorem projection_projective {P : Presentation} (R : StructuralRealization P) (n : ProjectionName) :
    Projection (projection R n) := by
  have hu (w : Word) : Unitary (evalWord (CompilerHonestDictionary.dictionary R) w) :=
    evalWord_unitary _ (CompilerHonestDictionary.dictionary_unitary R) w
  cases n with
  | parameter i => exact amplify_projection _ (CompilerHonestDictionary.parameter_projection i)
  | active g => exact amplify_projection _ (mask_projection 17 _)
  | frame i => exact lift_projection _ _ ⟨star_one Op,one_mul _⟩
  | graph w k part => exact inPair_projection _ _ (graphPart_projection _ (hu w) part)
  | triangle u v w => exact triangle_projection _ _ _ (hu u) (hu v) rfl
  | binding p i complement =>
      apply lift_projection
      cases complement
      · exact CompilerHonestDictionary.parameter_projection p
      · exact projection_compl _ (CompilerHonestDictionary.parameter_projection p)
  | joint p pair a b =>
      apply inPair_projection
      apply joint_projection
      split_ifs
      · exact CompilerHonestDictionary.parameter_projection p
      · exact projection_compl _ (CompilerHonestDictionary.parameter_projection p)


theorem inPair_zero (P : Op) : inPair 0 P=P := by
  have hp : RowCompleteness.permutationMatrix (1 : Equiv.Perm (Fin 3))=1 := by
    apply Matrix.ext
    intro i j
    simp [RowCompleteness.permutationMatrix,Matrix.one_apply,eq_comm]
  rw [inPair,pairPerm,if_pos rfl,permutation,hp,matrixOp_one,star_one,one_mul,mul_one]

theorem projection_graph_zero {P : Presentation} (R : StructuralRealization P) (w : Word) :
    projection R (.graph w 0 0)=
      matrixOp 3 (graphBlocks (evalWord (CompilerHonestDictionary.dictionary R) w)) := by
  change inPair 0 (graphPart _ 0)=_
  rw [inPair_zero,graphPart,if_pos rfl]

#print axioms projection_projective
end Sigma2.CompilerProjectionDictionary
