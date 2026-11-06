import Sigma2.CompilerSoundnessPadding
import Sigma2.RowSynchronization

/-! Binary events of the concrete scaffold: dictionary lookup and synchronization
on both original marginal supports. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessNames
open Compiler CompilerScaffold Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

def nameIndex (P : Presentation) (n : ProjectionName) (hn : n ∈ names P) : Fin (names P).length :=
  ⟨(names P).idxOf n,List.idxOf_lt_length_iff.mpr hn⟩

theorem get_nameIndex (P : Presentation) (n : ProjectionName) (hn : n ∈ names P) :
    (names P)[(nameIndex P n hn).val]=n := by
  exact List.getElem_idxOf (nameIndex P n hn).isLt

def namedEvent (P : Presentation) (n : ProjectionName) (hn : n ∈ names P) :
    NamedEvent (scenario P) := event P (nameIndex P n hn)

theorem question_event (P : Presentation) (i : Fin (names P).length) :
    question P (event P i).x.val=.binary ((names P)[i.val]) := by
  change question P i.val=_
  simp only [question,i.isLt,if_pos,List.getElem?_eq_getElem i.isLt,Option.getD_some]

theorem question_named (P : Presentation) (n : ProjectionName) (hn : n ∈ names P) :
    question P (namedEvent P n hn).x.val=.binary n := by
  rw [namedEvent,question_event,get_nameIndex]

theorem synchronized (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (i : Fin (names P).length) :
    BinaryEventSynchronized S (event P i) := by
  intro a b hab
  have hv : a.val≠b.val := by
    intro he
    apply hab
    simp only [event,Fin.ext_iff]
    omega
  apply pre_rejected_probability P S hS
  change rule P (question P (event P i).x.val) (question P (event P i).x.val) a.val b.val=false
  rw [question_event]
  simp [rule,hv]

theorem named (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) : NamedBinaryProjections (rows P) S :=
  RowSynchronization.named_of_synchronized (rows P) S (synchronized P S hS)

def projectionA (P : Presentation) (S : NormalStrategy (scenario P)) (e : Op)
    (n : ProjectionName) : Op :=
  if hn : n ∈ names P then e*S.measurements.alice (namedEvent P n hn).x 1*e else 0

def projectionB (P : Presentation) (S : NormalStrategy (scenario P)) (e : Op)
    (n : ProjectionName) : Op :=
  if hn : n ∈ names P then e*S.measurements.bob (namedEvent P n hn).y 1*e else 0

theorem projectionA_of_mem (P : Presentation) (S : NormalStrategy (scenario P)) (e : Op)
    (n : ProjectionName) (hn : n ∈ names P) :
    projectionA P S e n=e*S.measurements.alice (namedEvent P n hn).x 1*e := by
  simp only [projectionA,hn,dite_true]

theorem projectionB_of_mem (P : Presentation) (S : NormalStrategy (scenario P)) (e : Op)
    (n : ProjectionName) (hn : n ∈ names P) :
    projectionB P S e n=e*S.measurements.bob (namedEvent P n hn).y 1*e := by
  simp only [projectionB,hn,dite_true]

theorem sharpA (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (n : ProjectionName) : Projection (projectionA P S e n) := by
  by_cases hn : n ∈ names P
  · rw [projectionA_of_mem P S e n hn]
    exact (RowSynchronization.binary_alice S (namedEvent P n hn) h hm e he
      (synchronized P S hS (nameIndex P n hn))).1.2
  · simp only [projectionA,hn,dite_false]
    exact ⟨by rw [ContinuousLinearMap.star_eq_adjoint]; exact map_zero _,by exact zero_mul _⟩

theorem sharpB (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalB S h)
    (e : Op) (he : SupportOf h e) (n : ProjectionName) : Projection (projectionB P S e n) := by
  by_cases hn : n ∈ names P
  · rw [projectionB_of_mem P S e n hn]
    exact (RowSynchronization.binary_bob S (namedEvent P n hn) h hm e he
      (synchronized P S hS (nameIndex P n hn))).1.2
  · simp only [projectionB,hn,dite_false]
    exact ⟨by rw [ContinuousLinearMap.star_eq_adjoint]; exact map_zero _,by exact zero_mul _⟩

theorem centralA (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (n : ProjectionName) : Centralizes h.op (projectionA P S e n) := by
  by_cases hn : n ∈ names P
  · rw [projectionA_of_mem P S e n hn]
    exact ((MatrixCentralizer.support_centralizes h e he).mul_right
      (RowSynchronization.binary_alice S (namedEvent P n hn) h hm e he
        (synchronized P S hS (nameIndex P n hn))).2).mul_right
          (MatrixCentralizer.support_centralizes h e he)
  · simp only [projectionA,hn,dite_false]
    exact Commute.zero_right _

theorem centralB (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalB S h)
    (e : Op) (he : SupportOf h e) (n : ProjectionName) : Centralizes h.op (projectionB P S e n) := by
  by_cases hn : n ∈ names P
  · rw [projectionB_of_mem P S e n hn]
    exact ((MatrixCentralizer.support_centralizes h e he).mul_right
      (RowSynchronization.binary_bob S (namedEvent P n hn) h hm e he
        (synchronized P S hS (nameIndex P n hn))).2).mul_right
          (MatrixCentralizer.support_centralizes h e he)
  · simp only [projectionB,hn,dite_false]
    exact Commute.zero_right _

#print axioms synchronized
#print axioms named
#print axioms sharpA
#print axioms sharpB
#print axioms centralA
#print axioms centralB
end Sigma2.CompilerSoundnessNames
