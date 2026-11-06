import Sigma2.RowDiagonalEntries
import Sigma2.RowSlotLaws

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates

/-- A selfadjoint corner reflection extends by the identity on the orthogonal
    complement. This is the ambient unitary required by the matrix uniqueness API. -/
theorem corner_reflection_completion (e A : Op) (he : Projection e)
    (hs : star A=A) (hsq : A*A=e) (hL : e*A=A) (hR : A*e=A) :
    Unitary (A+(1-e)) := by
  have hstar : star (A+(1-e))=A+(1-e) := by
    rw [star_add A (1-e),star_sub (1:Op) e,star_one,he.1,hs]
  have hmul : (A+(1-e))*(A+(1-e))=1 := by
    simp only [add_mul,mul_add,sub_mul,mul_sub,mul_one,one_mul,hsq,hL,hR,he.2]
    noncomm_ring
  exact ⟨by rw [hstar,hmul],by rw [hstar,hmul]⟩

/-- Actual slot reflections commute with the numerically relabeled common units. -/
theorem slotReflection_numerical_commute (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (k l : Fin (RowSlots.dimension R)) :
    Commute (slotReflection bob G R S.measurements P r j) (numericalUnit bob G R S.measurements P k l) := by
  have hu := numericalUnit_laws bob G R S hS h hm P hP
  have hE : Commute (slotEvent bob G R S.measurements P r j)
      (numericalUnit bob G R S.measurements P k l) :=
    slotEvent_commute bob G R S hS h hm P hP r j _ _
  have hPc : Commute P (numericalUnit bob G R S.measurements P k l) :=
    (hu.supported k l).1.trans (hu.supported k l).2.symm
  exact (((hE.symm.smul_right (2:ℂ)).sub_right hPc.symm).smul_right
    (RowColumns.sign (RowSlots.slot R r j).negative)).symm

def slotCornerUnitary (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (r : Fin R.rowCount) (j : ℕ) : Op :=
  slotReflection bob G R M P r j*numericalUnit bob G R M P 0 0+
    (1-numericalUnit bob G R M P 0 0)

/-- The actual row coefficients give normalized corner unitaries for either
    original support, rather than assumed ambient unitaries. -/
theorem slotCornerUnitary_unitary (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) :
    Unitary (slotCornerUnitary bob G R S.measurements P r j) := by
  let A := slotReflection bob G R S.measurements P r j
  let e := numericalUnit bob G R S.measurements P 0 0
  have hu := numericalUnit_laws bob G R S hS h hm P hP
  have he : Projection e := hu.diagonal_projection 0
  have hA := slotReflection_laws bob G R S hS h hm P hP r j
  have hc : Commute A e := slotReflection_numerical_commute bob G R S hS h hm P hP r j 0 0
  apply corner_reflection_completion e (A*e) he
  · rw [star_mul,he.1,hA.1]
    exact hc.eq.symm
  · calc
      (A*e)*(A*e) = A*(e*A)*e := by noncomm_ring
      _ = A*(A*e)*e := by rw [← hc.eq]
      _ = (A*A)*(e*e) := by noncomm_ring
      _ = e := by rw [hA.2,he.2,(hu.supported 0 0).1]
  · rw [← mul_assoc,← hc.eq,mul_assoc,he.2]
  · rw [mul_assoc,he.2]

/-- The zero column label is precisely the required identity anchor. -/
theorem slotCornerUnitary_zero (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) : slotCornerUnitary bob G R S.measurements P r 0=1 := by
  have hu := numericalUnit_laws bob G R S hS h hm P hP
  have ha : slotReflection bob G R S.measurements P r 0=P := by
    have hh := slotReflection_anchor bob G R S.measurements P r 0 (by rw [RowSlots.slot_zero])
    simpa only [RowSlots.slot_zero,RowColumns.sign,Bool.false_eq_true,ite_false,one_smul] using hh
  rw [slotCornerUnitary,ha,(hu.supported 0 0).1]
  noncomm_ring

/-- The numerical 00 corner has the same faithful trace-one density and exact
    D normalization as the original support coordinates. -/
theorem numerical_corner_density (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P) :
    let e := numericalUnit bob G R S.measurements P 0 0
    ∃ h0 : Density,SupportOf h0 e ∧ h0.op=(RowSlots.dimension R:ℂ) • (h.op*e) := by
  have hu := numericalUnit_laws bob G R S hS h hm P hP
  have hc (i j : Fin (RowSlots.dimension R)) : Commute h.op (numericalUnit bob G R S.measurements P i j) := by
    cases bob
    · exact common_units_centralize G R S hS h hm P hP _ _
    · exact bob_units_centralize G R S hS h hm P hP _ _
  refine ⟨hu.cornerDensity h hP hc 0,hu.cornerDensity_support h hP hc 0,?_⟩
  change (Fintype.card (Fin (RowSlots.dimension R)):ℂ) •
    (h.op*numericalUnit bob G R S.measurements P 0 0)=_
  rw [Fintype.card_fin]

#print axioms corner_reflection_completion
#print axioms slotReflection_numerical_commute
#print axioms slotCornerUnitary_unitary
#print axioms slotCornerUnitary_zero
#print axioms numerical_corner_density
end Sigma2.RowScalar
