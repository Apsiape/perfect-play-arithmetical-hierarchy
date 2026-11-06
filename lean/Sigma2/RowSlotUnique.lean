import Sigma2.RowSlotBindings

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral FiniteJoint

/-- Support on both sides, for every coarsening of an actual new POVM. -/
theorem new_coarse_supported (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (hP : Projection P)
    (q : NewQ R) (f : Answer G R → Bool) (t : Bool) :
    P*coarse (newEffects bob G R M P q) f t=coarse (newEffects bob G R M P q) f t ∧
      coarse (newEffects bob G R M P q) f t*P=coarse (newEffects bob G R M P q) f t := by
  cases bob <;> simp only [newEffects,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,coarse_compressed]
  all_goals exact ⟨by simp only [← mul_assoc,hP.2],by simp only [mul_assoc,hP.2]⟩

theorem slot_class_reject {s} (R : Rows s) (r : Fin R.rowCount) (j c a b : ℕ)
    (hne : decide (a%3=c)≠decide (scalarClass b=c)) :
    newRule R (.slot r j) (.pair j) a b=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hd : directed R (.slot r j) (.pair j) a b=true := by
    simp only [newRule,Bool.and_eq_true] at hh
    exact hh.1.2
  have heq : a%3=scalarClass b := by
    simp only [directed,ite_true,Bool.and_eq_true,decide_eq_true_eq] at hd
    exact hd.1
  exact hne (by rw [heq])

/-- The canonical scalar-pair sector, with no slot effects in its definition. -/
def slotSector (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (j c : ℕ) : Op :=
  coarse (fun b : Answer G R => pairJoint bob G R M P j b.val)
    (fun b => decide (scalarClass b.val=c)) true

/-- Exact finite joint identification of all six slot effects, with zero for
all padded answers. The product order is part of the proved formula. -/
theorem slot_unique (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (a : Answer G R) :
    newEffects bob G R S.measurements P (slotQ R r j hj) a=
      if a.val<6 then
        (if a.val/3=1 then slotEvent bob G R S.measurements P r j
          else P-slotEvent bob G R S.measurements P r j) *
        slotSector bob G R S.measurements P j (a.val%3)
      else 0 := by
  let B := newEffects bob G R S.measurements P (slotQ R r j hj)
  let f : Bool → Answer G R → Bool := fun k b =>
    if k then decide (b.val%3=a.val%3) else decide (b.val/3=1)
  have hc := new_coarse_eq bob G R S hS h hm P hP (slotQ R r j hj) (pairQ R j hj)
    (fun b => decide (b%3=a.val%3)) (fun b => decide (scalarClass b=a.val%3))
    (slot_class_reject R r j (a.val%3)) true
  have hp (k : Bool) : Projection (coarse B (f k) (f k a)) := by
    cases k
    · exact (new_coarse_eq bob G R S hS h hm P hP (slotQ R r j hj) (slotQ R r j hj)
        (fun b => decide (b/3=1)) (fun b => decide (b/3=1)) (by
          intro b c hab
          apply Bool.eq_false_iff.mpr
          intro hh
          have heq : b=c := by
            simp only [newRule,Bool.and_eq_true,ite_true,decide_eq_true_eq] at hh
            exact hh.1.1.2
          exact hab (by rw [heq])) (f false a)).2
    · simpa [B,f] using hc.2
  by_cases ha : a.val<6
  · rw [if_pos ha]
    have he := fine_unique B P hP.1
      (new_positive bob G R S.measurements P hP.1 _) (new_sum bob G R S.measurements P hP.1 _)
      (fun b => b.val<6)
      (fun b hb => new_invalid_zero bob G R S hS h hm P hP _ b (by simp [slotQ,valid,hb]))
      f [false,true] a hp ha (by
        intro b hb heq
        apply Fin.ext
        have hq := heq false (by simp)
        have hr := heq true (by simp)
        simp only [f,Bool.false_eq_true,ite_false,Bool.true_eq,ite_true,decide_true] at hq hr
        have hrem : b.val%3=a.val%3 := by simpa using hr
        have hquot : b.val/3=1 ↔ a.val/3=1 := by simpa using hq
        omega)
    change B a=_
    rw [he]
    simp only [intersection,List.isEmpty_cons,Bool.false_eq_true,ite_false,Bool.true_eq,ite_true,f,decide_true]
    rw [(new_coarse_supported bob G R S.measurements P hP.1 (slotQ R r j hj)
      (fun b => decide (b.val%3=a.val%3)) true).2]
    rw [slot_event_marginal bob G R S hS h hm P hP,hc.1]
    simp only [decide_eq_true_eq]
    apply congrArg (fun C : Op => (if a.val/3=1 then slotEvent bob G R S.measurements P r j
      else P-slotEvent bob G R S.measurements P r j)*C)
    exact congrArg (fun E : Answer G R → Op => coarse E (fun b => decide (scalarClass b.val=a.val%3)) true)
      (funext (fun b => pair_unique bob G R S hS h hm P hP j hj b))
  · rw [if_neg ha]
    exact new_invalid_zero bob G R S hS h hm P hP _ a (by simp [slotQ,valid,ha])

/-- The signed slot graph formulas are in exactly the previously constructed
common scalar coordinates, for Alice or the reversed-word Bob units. -/
theorem slot_coordinates (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    {ι : Type} [Fintype ι] [DecidableEq ι] {t : ι → ι → Op}
    (hu : MatrixSupportCoordinates.Units P t) (o : ι)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (a : Answer G R) :
    coordinateAction hu o (newEffects bob G R S.measurements P (slotQ R r j hj) a)=
      coordinateAction hu o (if a.val<6 then
        (if a.val/3=1 then slotEvent bob G R S.measurements P r j
          else P-slotEvent bob G R S.measurements P r j) *
        slotSector bob G R S.measurements P j (a.val%3) else 0) := by
  rw [slot_unique bob G R S hS h hm P hP]

#print axioms new_coarse_supported
#print axioms slot_class_reject
#print axioms slot_unique
#print axioms slot_coordinates
end Sigma2.RowScalar




