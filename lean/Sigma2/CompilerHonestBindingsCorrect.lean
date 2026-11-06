import Sigma2.CompilerHonestBindings
import Sigma2.CompilerOrientedProjections
noncomputable section
namespace Sigma2.CompilerHonestBindingsCorrect
open Compiler CompilerScaffold CompilerOrientedProjections CompilerHonestState
  CompilerHonestFMSLift CompilerHonestRefinementCommute CoefficientOperator
  RowCompleteness TensorLifts
abbrev answer := CompilerHonestBindings.answer
def bindingVector {P : Presentation} (R : StructuralRealization P)
    (bob : Bool) (g : Fin 4) (x : Fin 5) (n : ProjectionName) (a : Fin 6) (b : Bool) : AB :=
  if bob then
    (left ((Partition.binary (CompilerOrientedProjections.projection R n) (CompilerOrientedProjections.projection_projective R n).1
      (CompilerOrientedProjections.projection_projective R n).2).effect b)*right ((fms true g x).effect a))
      (vector (density R.density))
  else
    (left ((fms false g x).effect a)*right ((Partition.binary (transpose (CompilerOrientedProjections.projection R n))
      (transpose_projection _ (CompilerOrientedProjections.projection_projective R n)).1
      (transpose_projection _ (CompilerOrientedProjections.projection_projective R n)).2).effect b))
      (vector (density R.density))

theorem binding_accepts {P : Presentation} (R : StructuralRealization P)
    (bob : Bool) (g : Fin 4) (x : Fin 5) (n : ProjectionName) (a : Fin 6) (b : Bool)
    (hne : bindingVector R bob g x n a b≠0) :
    fmsBinding (!bob) g.val x.val n a.val (answer b)=true := by
  cases n with
  | parameter i => exact CompilerHonestBindings.binding_accepts R bob g x (.parameter i) a b hne
  | active g' => exact CompilerHonestBindings.binding_accepts R bob g x (.active g') a b hne
  | frame i => simp [fmsBinding]
  | graph w k p => simp [fmsBinding]
  | triangle u v w => simp [fmsBinding]
  | binding p i c => simp [fmsBinding]
  | joint p k a' b' => simp [fmsBinding]
#print axioms binding_accepts
end Sigma2.CompilerHonestBindingsCorrect
