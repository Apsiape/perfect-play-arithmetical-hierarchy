import Sigma2.CompilerHonestCentralizer

/-! A single pregame dictionary and state, with independently supplied label
refinements. All four FMS instances and every named binary projection are
verified for this same strategy, regardless of the remaining refinements. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 500
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerHonestPregame
open Compiler CompilerScaffold CompilerHonestState CompilerHonestFMSLift
  CompilerProjectionDictionary CompilerHonestCentralizer CoefficientOperator
  TensorLifts RowCompleteness
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials
abbrev Answers := Fin 12
abbrev Refinements := ℕ → ℕ → Partition Op Answers

def bit (b : Bool) : Answers := if b then 1 else 0

def binary (E : Op) (hE : Projection E) : Partition Op Answers :=
  (Partition.binary E hE.1 hE.2).coarse bit

theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]

theorem binary_one (E : Op) (hE : Projection E) : (binary E hE).effect 1=E :=
  (Partition.coarse_injective _ bit bit_injective true).trans rfl

def pad (P : Partition Op (Fin 6)) : Partition Op Answers :=
  P.coarse (fun a => ⟨a.val,by have := a.isLt; omega⟩)

theorem pad_effect (P : Partition Op (Fin 6)) (a : Fin 6) :
    (pad P).effect ⟨a.val,by have := a.isLt; omega⟩=P.effect a := by
  exact Partition.coarse_injective P
    (fun a : Fin 6 => (⟨a.val,by have := a.isLt; omega⟩ : Answers))
    (by
      intro a b h
      apply Fin.ext
      exact congrArg (fun x : Answers => x.val) h) a

def localPartition {P : Presentation} (R : StructuralRealization P)
    (bob : Bool) (F : Refinements) : Question → Partition Op Answers
  | .binary n => if bob then binary (transpose (projection R n))
      (transpose_projection _ (projection_projective R n))
    else binary (projection R n) (projection_projective R n)
  | .fms g x => if hg : g<4 then if hx : x<5 then
      pad (if bob then CompilerHonestFMSLift.bob ⟨g,hg⟩ ⟨x,hx⟩
        else CompilerHonestFMSLift.alice ⟨g,hg⟩ ⟨x,hx⟩)
    else Partition.deterministic 0 else Partition.deterministic 0
  | .refinement g k => F g k
  | .padding => Partition.deterministic 0

def measurements {P : Presentation} (R : StructuralRealization P) (A B : Refinements) :
    Measurements (scenario P) :=
  TensorLifts.measurements _
    (fun x => (localPartition R false A (question P x.val)).effect)
    (fun y => (localPartition R true B (question P y.val)).effect)
    (fun x => (localPartition R false A (question P x.val)).positive)
    (fun y => (localPartition R true B (question P y.val)).positive)
    (fun x => (localPartition R false A (question P x.val)).total)
    (fun y => (localPartition R true B (question P y.val)).total)

def strategy {P : Presentation} (R : StructuralRealization P) (A B : Refinements) :
    NormalStrategy (scenario P) :=
  CompilerHonestState.strategy (density R.density) (measurements R A B)

theorem fmsA {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (g : Fin 4) (x : Fin 5) (a : Fin 6) :
    (strategy R A B).measurements.alice ((fmsInstance P g).qA x) ((fmsInstance P g).aA a)=
      (CompilerHonestFMSLift.alice g x).effect a := by
  change (localPartition R false A (question P ((names P).length+5*g.val+x.val))).effect _=_
  rw [question_fms]
  simp only [localPartition,Bool.false_eq_true,ite_false,dif_pos g.isLt,dif_pos x.isLt]
  exact pad_effect _ a

theorem fmsB {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (g : Fin 4) (x : Fin 5) (a : Fin 6) :
    (strategy R A B).measurements.bob ((fmsInstance P g).qB x) ((fmsInstance P g).aB a)=
      (CompilerHonestFMSLift.bob g x).effect a := by
  change (localPartition R true B (question P ((names P).length+5*g.val+x.val))).effect _=_
  rw [question_fms]
  simp only [localPartition,ite_true,dif_pos g.isLt,dif_pos x.isLt]
  exact pad_effect _ a

/-- Four simultaneous actual ConditionalPerfect witnesses on one strategy. -/
theorem conditionalPerfect {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (g : Fin 4) : ConditionalPerfect (strategy R A B) (fmsInstance P g) := by
  refine ⟨?_,?_,?_⟩
  · intro x y a b hr
    rw [strategy,CompilerHonestState.strategy,normalOfPure_probability]
    change (inner ℂ (CompilerHonestState.vector (density R.density))
      (((measurements R A B).left _ _*(measurements R A B).right _ _)
        (CompilerHonestState.vector (density R.density)))).re=0
    rw [measurements_left,measurements_right]
    have ha := fmsA R A B g x a
    have hb := fmsB R A B g y b
    change (measurements R A B).alice _ _=_ at ha
    change (measurements R A B).bob _ _=_ at hb
    rw [ha,hb,CompilerHonestFMSLift.rejection R.density g x y a b hr,inner_zero_right]
    rfl
  · intro x
    calc
      _=∑ a : Fin 6,(CompilerHonestFMSLift.alice g x).effect a :=
        Finset.sum_congr rfl (fun a _ => fmsA R A B g x a)
      _=1 := (CompilerHonestFMSLift.alice g x).total
  · intro y
    calc
      _=∑ a : Fin 6,(CompilerHonestFMSLift.bob g y).effect a :=
        Finset.sum_congr rfl (fun a _ => fmsB R A B g y a)
      _=1 := (CompilerHonestFMSLift.bob g y).total

theorem question_name (P : Presentation) (i : Fin (names P).length) :
    question P i.val=.binary ((names P)[i.val]'i.isLt) := by
  simp only [question,if_pos i.isLt,List.getElem?_eq_getElem i.isLt,Option.getD_some]

theorem namedA {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (i : Fin (names P).length) :
    (strategy R A B).measurements.alice (event P i).x (event P i).a=
      projection R ((names P)[i.val]'i.isLt) := by
  change (localPartition R false A (question P i.val)).effect 1=_
  rw [question_name]
  exact binary_one _ (projection_projective R _)

theorem namedB {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (i : Fin (names P).length) :
    (strategy R A B).measurements.bob (event P i).y (event P i).b=
      transpose (projection R ((names P)[i.val]'i.isLt)) := by
  change (localPartition R true B (question P i.val)).effect 1=_
  rw [question_name]
  exact binary_one _ (transpose_projection _ (projection_projective R _))

theorem named_mirror {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (i : Fin (names P).length) (k : ℕ) :
    (strategy R A B).measurements.left (event P i).x (event P i).a ((strategy R A B).vector k)=
      (strategy R A B).measurements.right (event P i).y (event P i).b ((strategy R A B).vector k) := by
  rw [measurements_left,measurements_right,namedA,namedB]
  exact mirror _ _ (projection_centralizer R _)

#print axioms conditionalPerfect
#print axioms named_mirror
end Sigma2.CompilerHonestPregame
