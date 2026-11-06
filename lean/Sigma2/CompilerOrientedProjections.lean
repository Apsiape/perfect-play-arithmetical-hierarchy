import Sigma2.CompilerHonestPairs
import Sigma2.CompilerHonestRefinementCommute

/-! A new corrected dictionary. The old k=2 graphs and joints are conjugated
 once more by the old qutrit cycle, giving the required (1,2) ordered pair. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerOrientedProjections
open Compiler CompilerScaffold CompilerProjectionDictionary CompilerFiniteRegister
  CompilerHonestCentralizer CompilerHonestRefinementCommute CompilerHonestCommute
  CompilerHonestFMSLift FiniteAncilla RowCompleteness

def repair : ProjectionName → Bool
  | .graph _ k _ => decide (k=2)
  | .joint _ k _ _ => decide (k=2)
  | _ => false

def projection {P : Presentation} (R : StructuralRealization P) (n : ProjectionName) : Op :=
  if repair n then inPair 2 (CompilerProjectionDictionary.projection R n)
    else CompilerProjectionDictionary.projection R n

theorem projection_projective {P : Presentation} (R : StructuralRealization P) (n : ProjectionName) :
    Projection (projection R n) := by
  unfold projection
  split_ifs
  · exact inPair_projection _ _ (CompilerProjectionDictionary.projection_projective R n)
  · exact CompilerProjectionDictionary.projection_projective R n

theorem projection_centralizer {P : Presentation} (R : StructuralRealization P) (n : ProjectionName) :
    Centralizes (density R.density).op (projection R n) := by
  unfold projection
  split_ifs
  · exact qutrit_pair _ _ _ (CompilerHonestCentralizer.projection_centralizer R n)
  · exact CompilerHonestCentralizer.projection_centralizer R n

theorem cycle_commute (T : Op) : Commute (amplify 3 T) (permutation 3 (pairPerm 2)) := by
  apply amplify_matrix_commute
  intro i j
  simp only [permutationMatrix,Matrix.of_apply]
  split_ifs <;> first | exact Commute.one_right T | exact Commute.zero_right T

theorem cycle_star_commute (T : Op) : Commute (amplify 3 T) (star (permutation 3 (pairPerm 2))) := by
  rw [permutation,← matrixOp_star,permutation_star]
  apply amplify_matrix_commute
  intro i j
  simp only [permutationMatrix,Matrix.of_apply]
  split_ifs <;> first | exact Commute.one_right T | exact Commute.zero_right T

theorem commute_corrected {P : Presentation} (R : StructuralRealization P) (T : Op) (n : ProjectionName)
    (hc : Commute (amplify 3 T) (CompilerProjectionDictionary.projection R n)) :
    Commute (amplify 3 T) (projection R n) := by
  unfold projection
  split_ifs
  · exact ((cycle_commute T).mul_right hc).mul_right (cycle_star_commute T)
  · exact hc

/-- The correction keeps every separate FMS-label joint valid. -/
theorem label_commute {P : Presentation} (R : StructuralRealization P) (g : Fin 4)
    (k : Fin (6+encodingCount P)) (bob : Bool) (x : Fin 5) (a : Fin 6) :
    Commute ((fms bob g x).effect a) (projection R (refinementLabel P g.val k.val)) := by
  rw [fms_effect]
  apply commute_corrected
  simpa only [fms_effect] using CompilerHonestRefinementCommute.label_commute R g k bob x a

theorem bob_label_commute {P : Presentation} (R : StructuralRealization P) (g : Fin 4)
    (k : Fin (6+encodingCount P)) (x : Fin 5) (a : Fin 6) :
    Commute ((fms true g x).effect a) (CoefficientOperator.transpose (projection R (refinementLabel P g.val k.val))) := by
  apply transpose_commute _ _ _ (label_commute R g k true x a)
  rw [fms_effect,CompilerHonestFMSLift.transpose_amplify,core_transpose]

theorem projection_graph_zero {P : Presentation} (R : StructuralRealization P) (w : Word) :
    projection R (.graph w 0 0)=matrixOp 3
      (CompilerHonestQutrit.graphBlocks (evalWord (CompilerHonestDictionary.dictionary R) w)) :=
  CompilerProjectionDictionary.projection_graph_zero R w

/-- The corrected actual named graphs use the frozen row's frames 1 and 2. -/
theorem graph_two_sum {P : Presentation} (R : StructuralRealization P) (w : Word) :
    projection R (.graph w 2 0)+projection R (.graph w 2 1)=frame 1+frame 2 := by
  change inPair 2 (CompilerProjectionDictionary.projection R (.graph w 2 0))+
    inPair 2 (CompilerProjectionDictionary.projection R (.graph w 2 1))=_
  rw [← CompilerHonestPairs.inPair_add,CompilerHonestPairs.old_graph_two_sum,
    ← CompilerHonestPairs.old_pair_two_frame,CompilerHonestPairs.inPair_matrix,
    CompilerHonestPairs.inPair_matrix]
  change matrixOp 3 _=matrixOp 3 (CompilerApproxBlocks.singleBlocks 3 1 1 1)+
    matrixOp 3 (CompilerApproxBlocks.singleBlocks 3 2 2 1)
  rw [← matrixOp_add]
  congr 1
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pairPerm,CompilerHonestQutrit.pairFrame,Equiv.swap_apply_def,
      CompilerApproxBlocks.singleBlocks]

#print axioms projection_projective
#print axioms projection_centralizer
#print axioms label_commute
end Sigma2.CompilerOrientedProjections
