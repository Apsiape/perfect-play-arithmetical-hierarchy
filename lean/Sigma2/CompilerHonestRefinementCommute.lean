import Sigma2.CompilerHonestCommute

/-! Commutation of every literal refinement label with the scalar FMS
 measurement that it refines, on both actual tensor factors. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestRefinementCommute
open Compiler CompilerScaffold CompilerHonestCommute CompilerHonestScalar
  CompilerHonestDictionary CompilerProjectionDictionary CompilerHonestFMSLift
  CompilerHonestQutrit CompilerFiniteRegister CompilerHonestLift
  CoefficientOperator FiniteAncilla RowCompleteness
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

def fms (bob : Bool) (g : Fin 4) (x : Fin 5) : Partition Op (Fin 6) :=
  if bob then CompilerHonestFMSLift.bob g x else CompilerHonestFMSLift.alice g x

def core (bob : Bool) (g : Fin 4) (x : Fin 5) (a : Fin 6) : Op :=
  scalarOp 17 ((if bob then CompilerHonestFamilies.bob g x
    else CompilerHonestFamilies.alice g x).effect a)

theorem fms_effect (bob : Bool) (g : Fin 4) (x : Fin 5) (a : Fin 6) :
    (fms bob g x).effect a=amplify 3 (core bob g x a) := by cases bob <;> rfl

theorem core_star (bob : Bool) (g : Fin 4) (x : Fin 5) (a : Fin 6) :
    star (core bob g x a)=core bob g x a := by
  change star (scalarOp 17 _)=scalarOp 17 _
  rw [← scalar_star]
  congr 1
  exact (if bob then CompilerHonestFamilies.bob g x else
    CompilerHonestFamilies.alice g x).selfadjoint a

theorem core_transpose (bob : Bool) (g : Fin 4) (x : Fin 5) (a : Fin 6) :
    transpose (core bob g x a)=core bob g x a := by
  unfold core
  rw [transpose_scalar]
  congr 1
  cases bob
  all_goals
    simp only [Bool.false_eq_true,ite_false,ite_true,
      CompilerHonestFMSWeights.alice_effect,CompilerHonestFMSWeights.bob_effect]
    rw [Matrix.transpose_add,CompilerHonestFMSWeights.embed_transpose]
    congr 1
    · congr 1
      exact CompilerHonestFMS.rankOne_transpose _
    · split_ifs <;> simp [CompilerHonestFMSWeights.active,
        CompilerHonestFMSWeights.embed_transpose]

theorem star_right (T U : Op) (hs : star T=T) (hc : Commute T U) : Commute T (star U) := by
  have h := congrArg (fun V : Op => star V) hc.eq
  change T*star U=star U*T
  simpa only [star_mul,hs] using h.symm

theorem graph_commute (T U : Op) (hs : star T=T) (hc : Commute T U) :
    Commute (amplify 3 T) (matrixOp 3 (graphBlocks U)) := by
  apply amplify_matrix_commute
  intro i j
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (Commute.one_right T).smul_right (1/2:ℂ)
    | exact hc.smul_right (1/2:ℂ)
    | exact (star_right T U hs hc).smul_right (1/2:ℂ)
    | exact Commute.zero_right T

theorem frame_commute (T : Op) (k : ℕ) : Commute (amplify 3 T) (frame k) := by
  apply amplify_matrix_commute
  intro i j
  simp only [CompilerApproxBlocks.singleBlocks]
  split_ifs <;> first | exact Commute.one_right T | exact Commute.zero_right T

theorem emptyGraph_commute (T : Op) (k : ℕ) :
    Commute (amplify 3 T) (inPair k (graphPart 1 0)) := by
  have hp : Commute (amplify 3 T) (permutation 3 (pairPerm k)) := by
    apply amplify_matrix_commute
    intro i j
    simp only [RowCompleteness.permutationMatrix,Matrix.of_apply]
    split_ifs <;> first | exact Commute.one_right T | exact Commute.zero_right T
  have hps : Commute (amplify 3 T) (star (permutation 3 (pairPerm k))) := by
    rw [permutation,← matrixOp_star,RowCompleteness.permutation_star]
    apply amplify_matrix_commute
    intro i j
    simp only [RowCompleteness.permutationMatrix,Matrix.of_apply]
    split_ifs <;> first | exact Commute.one_right T | exact Commute.zero_right T
  have hg : Commute (amplify 3 T) (graphPart 1 0) := by
    rw [graphPart,if_pos rfl]
    apply amplify_matrix_commute
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [graphBlocks,Commute,SemiconjBy,mul_smul_comm,smul_mul_assoc]
  exact (hp.mul_right hg).mul_right hps

/-- Only a single label is joined with a scalar FMS partition. -/
theorem label_commute {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (bob : Bool) (x : Fin 5) (a : Fin 6) :
    Commute ((fms bob g x).effect a) (projection R (refinementLabel P g.val k.val)) := by
  rw [fms_effect]
  unfold refinementLabel
  split_ifs with hk3 hk6
  · exact frame_commute _ _
  · change Commute _ (inPair _ (graphPart (evalWord (dictionary R) []) 0))
    exact emptyGraph_commute _ _
  · have hk := k.isLt
    have he : k.val-6<encodingCount P := by omega
    change Commute _ (inPair 0 (graphPart _ 0))
    rw [inPair_zero,graphPart,if_pos rfl,eval_block R g ⟨k.val-6,he⟩]
    exact graph_commute _ _ (core_star bob g x a) (fms_repeated_commute g bob x a _)

theorem transpose_commute (T E : Op) (ht : transpose T=T) (hc : Commute T E) :
    Commute T (transpose E) := by
  have h := congrArg transpose hc.eq
  change T*transpose E=transpose E*T
  simpa only [CompilerHonestState.transpose_mul,ht] using h.symm

/-- Bob uses the genuine coordinate transpose of the same label. -/
theorem bob_label_commute {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (x : Fin 5) (a : Fin 6) :
    Commute ((fms true g x).effect a) (transpose (projection R (refinementLabel P g.val k.val))) := by
  apply transpose_commute _ _ _ (label_commute R g k true x a)
  rw [fms_effect,transpose_amplify,core_transpose]

#print axioms label_commute
#print axioms bob_label_commute
end Sigma2.CompilerHonestRefinementCommute
