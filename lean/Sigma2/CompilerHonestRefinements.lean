import Sigma2.CompilerHonestRefinementAlgebra
import Sigma2.CompilerHonestRefinementCommute

/-! Actual separate refinement partitions supplied from an arbitrary structural
 realization, with all retained FMS rejections on the common purification. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestRefinements
open Compiler CompilerScaffold CompilerHonestState CompilerHonestFMSLift
  CompilerProjectionDictionary CompilerHonestCentralizer CoefficientOperator
  CompilerHonestRefinementCommute CompilerHonestRefinementAlgebra
  RowCompleteness TensorLifts
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

def label {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) : Op :=
  projection R (refinementLabel P g.val k.val)

def alice {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) : Partition Op (Fin 12) :=
  refine (fms false g 3) (label R g k) (projection_projective R _)
    (label_commute R g k false 3)

def bob {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) : Partition Op (Fin 12) :=
  refine (fms true g 3) (transpose (label R g k))
    (transpose_projection _ (projection_projective R _)) (bob_label_commute R g k 3)

def refinements {P : Presentation} (R : StructuralRealization P) (isBob : Bool) :
    CompilerHonestPregame.Refinements := fun g k =>
  if hg : g<4 then if hk : k<6+encodingCount P then
    if isBob then bob R ⟨g,hg⟩ ⟨k,hk⟩ else alice R ⟨g,hg⟩ ⟨k,hk⟩
  else Partition.deterministic 0 else Partition.deterministic 0

def strategy {P : Presentation} (R : StructuralRealization P) : NormalStrategy (scenario P) :=
  CompilerHonestPregame.strategy R (refinements R false) (refinements R true)

theorem alice_effect {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (a : Fin 12) :
    (alice R g k).effect a=(CompilerHonestFMSLift.alice g 3).effect (unpack a).1*
      (if (unpack a).2 then label R g k else 1-label R g k) :=
  refine_effect _ _ _ _ a

theorem bob_effect {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (a : Fin 12) :
    (bob R g k).effect a=(CompilerHonestFMSLift.bob g 3).effect (unpack a).1*
      (if (unpack a).2 then transpose (label R g k) else 1-transpose (label R g k)) :=
  refine_effect _ _ _ _ a

/-- Includes every retained y=0,3,4 check, and indeed every conditional FMS
 rejection involving Alice's refined question 3. -/
theorem alice_rejection {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (y : Fin 5) (a : Fin 12) (b : Fin 6)
    (hr : conditionalFmsRule 3 y.val (a.val/2) b.val=false) :
    (left ((alice R g k).effect a)*right ((CompilerHonestFMSLift.bob g y).effect b))
      (vector (density R.density))=0 := by
  apply event_zero
  apply refine_left_zero
  exact rejection_coefficient R.density g 3 y (unpack a).1 b hr

/-- Every retained reverse-orientation check uses Bob's genuine refinement. -/
theorem bob_rejection {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (x : Fin 5) (a : Fin 6) (b : Fin 12)
    (hr : conditionalFmsRule x.val 3 a.val (b.val/2)=false) :
    (left ((CompilerHonestFMSLift.alice g x).effect a)*right ((bob R g k).effect b))
      (vector (density R.density))=0 := by
  apply event_zero
  apply refine_right_zero
  exact rejection_coefficient R.density g x 3 a (unpack b).1 hr

 theorem binary_label_mirror {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (b : Bool) :
    left ((Partition.binary (label R g k) (projection_projective R _).1
      (projection_projective R _).2).effect b) (vector (density R.density))=
    right ((Partition.binary (transpose (label R g k))
      (transpose_projection _ (projection_projective R _)).1
      (transpose_projection _ (projection_projective R _)).2).effect b)
      (vector (density R.density)) := by
  exact binary_mirror _ _ (projection_projective R _)
    (transpose_projection _ (projection_projective R _)) _
    (mirror _ _ (projection_centralizer R _)) b

 theorem alice_label_rejection {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (a : Fin 12) (b : Bool)
    (hr : ¬ ((a.val%2=1) ↔ b=true)) :
    (left ((alice R g k).effect a)*right
      ((Partition.binary (transpose (label R g k))
        (transpose_projection _ (projection_projective R _)).1
        (transpose_projection _ (projection_projective R _)).2).effect b))
      (vector (density R.density))=0 := by
  have hne : (unpack a).2≠b := by
    intro h
    apply hr
    rw [← h]
    simp [unpack]
  change left _ (right _ (vector _))=0
  rw [← binary_label_mirror R g k b,← mul_apply_eq_comp,← left_mul]
  rw [show (alice R g k).effect a*_=0 from refine_label_zero _ _ _ _ a b hne,
    CoarseCells.left_zero,zero_apply]

 theorem bob_label_rejection {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin (6+encodingCount P)) (a : Bool) (b : Fin 12)
    (hr : ¬ ((b.val%2=1) ↔ a=true)) :
    (left ((Partition.binary (label R g k) (projection_projective R _).1
      (projection_projective R _).2).effect a)*right ((bob R g k).effect b))
      (vector (density R.density))=0 := by
  have hne : (unpack b).2≠a := by
    intro h
    apply hr
    rw [← h]
    simp [unpack]
  rw [TensorLifts.commute]
  change right _ (left _ (vector _))=0
  rw [binary_label_mirror R g k a,← mul_apply_eq_comp,← right_mul]
  rw [show (bob R g k).effect b*_=0 from refine_label_zero _ _ _ _ b a hne,
    CoarseCells.right_zero,zero_apply]

 theorem conditionalPerfect {P : Presentation} (R : StructuralRealization P) (g : Fin 4) :
    ConditionalPerfect (strategy R) (fmsInstance P g) :=
  CompilerHonestPregame.conditionalPerfect R _ _ g

 theorem namedBinaryProjections {P : Presentation} (R : StructuralRealization P) :
    NamedBinaryProjections (rows P) (strategy R) :=
  CompilerHonestNamed.namedBinaryProjections R _ _

#print axioms alice_rejection
#print axioms bob_rejection
#print axioms alice_label_rejection
#print axioms bob_label_rejection
#print axioms namedBinaryProjections
end Sigma2.CompilerHonestRefinements
