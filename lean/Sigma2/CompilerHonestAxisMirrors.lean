import Sigma2.CompilerHonestAxes
import Sigma2.CompilerHonestPregame

/-! Positive-axis binding in the actual numbered pregame questions, including
Bob's genuine transpose convention. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestAxisMirrors
open Compiler CompilerScaffold CompilerHonestAxes CompilerHonestFMSLift
  CompilerHonestScalar CompilerHonestState CompilerProjectionDictionary
  CompilerHonestPregame CoefficientOperator FiniteAncilla
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

theorem local_parameter_transpose (k : Fin 2) :
    (CompilerHonestFMS.parameter k).transpose=CompilerHonestFMS.parameter k := by
  apply Matrix.ext
  intro i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num [CompilerHonestFMS.parameter]

theorem axis_transpose (g : Fin 4) (k : Fin 2) :
    transpose (CompilerHonestDictionary.parameter (17+2*g.val+k.val))=
      CompilerHonestDictionary.parameter (17+2*g.val+k.val) := by
  rw [← actual_axis,transpose_scalar,CompilerHonestFMSWeights.embed_transpose,
    local_parameter_transpose]

/-- The frozen Alice coarse event equals its actual numbered projection. -/
theorem alice_axis {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (g : Fin 4) (k : Fin 2) :
    (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false
      then (CompilerHonestPregame.strategy R A B).measurements.alice
        ((fmsInstance P g).qA (if k=0 then 1 else 0)) ((fmsInstance P g).aA a) else 0)=
      projection R (.parameter (17+2*g.val+k.val)) := by
  calc
    _=∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false
      then (CompilerHonestFMSLift.alice g (if k=0 then 1 else 0)).effect a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases he : 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false
        · rw [if_pos he,if_pos he]
          exact fmsA R A B g (if k=0 then 1 else 0) a
        · rw [if_neg he,if_neg he]
    _=_ := CompilerHonestAxes.alice_axis_binding g k

/-- Bob's actual coarse event is the transposed numbered binary value. -/
theorem bob_axis {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (g : Fin 4) (k : Fin 2) :
    (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧
      cellSign false (a.val-1) (if k=0 then 1 else 0)=false
      then (CompilerHonestPregame.strategy R A B).measurements.bob
        ((fmsInstance P g).qB 1) ((fmsInstance P g).aB a) else 0)=
      transpose (projection R (.parameter (17+2*g.val+k.val))) := by
  calc
    _=∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧
      cellSign false (a.val-1) (if k=0 then 1 else 0)=false
      then (CompilerHonestFMSLift.bob g 1).effect a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases he : 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) (if k=0 then 1 else 0)=false
        · rw [if_pos he,if_pos he]
          exact fmsB R A B g 1 a
        · rw [if_neg he,if_neg he]
    _=amplify 3 (CompilerHonestDictionary.parameter (17+2*g.val+k.val)) :=
      CompilerHonestAxes.bob_axis_binding g k
    _=_ := by
      change amplify 3 _=transpose (amplify 3 _)
      rw [transpose_amplify,axis_transpose]

#print axioms axis_transpose
#print axioms alice_axis
#print axioms bob_axis
end Sigma2.CompilerHonestAxisMirrors
