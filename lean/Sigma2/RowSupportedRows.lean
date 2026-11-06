import Sigma2.RowActualColumnUnique
import Sigma2.RowSoundness

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates RowColumns

/-- A supported element of the scalar commutant is determined by its 00
    corner; this returns from corner equations to the original support. -/
theorem central_zero_of_corner {d : ℕ} (P : Op) (t : Fin d → Fin d → Op)
    (hu : Units P t) (o : Fin d) (A : Op) (hR : A*P=A)
    (hc : ∀ i j,Commute A (t i j)) (hz : A*t o o=0) : A=0 := by
  have hi (i : Fin d) : A*t i i=0 := by
    calc
      A*t i i = A*(t i o*t o i) := by rw [hu.product,if_pos rfl]
      _ = t i o*A*t o i := by rw [← mul_assoc,(hc i o).eq]
      _ = t i o*(A*(t o o*t o i)) := by rw [hu.product,if_pos rfl]; noncomm_ring
      _ = t i o*(A*t o o)*t o i := by noncomm_ring
      _ = 0 := by rw [hz,mul_zero,zero_mul]
  calc
    A = A*P := hR.symm
    _ = ∑ i,A*t i i := by rw [← Finset.mul_sum,hu.total]
    _ = 0 := by simp only [hi,Finset.sum_const_zero]

theorem slotReflection_supported (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) :
    slotReflection bob G R S.measurements P r j*P=slotReflection bob G R S.measurements P r j := by
  rw [slotReflection,smul_mul_assoc,sub_mul,smul_mul_assoc,
    (slotEvent_laws bob G R S hS h hm P hP r j).2.2,hP.1.2]

/-- The complete supported sum of the actual signed slots vanishes. -/
theorem actual_support_row_sum (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) :
    (∑ j : Fin (RowSlots.dimension R),slotReflection bob G R S.measurements P r j.val)=0 := by
  apply central_zero_of_corner P _ (numericalUnit_laws bob G R S hS h hm P hP) 0
  · simp only [Finset.sum_mul,slotReflection_supported bob G R S hS h hm P hP]
  · intro i j
    change (∑ k : Fin (RowSlots.dimension R),slotReflection bob G R S.measurements P r k.val)*
      numericalUnit bob G R S.measurements P i j=
      numericalUnit bob G R S.measurements P i j*(∑ k : Fin (RowSlots.dimension R),slotReflection bob G R S.measurements P r k.val)
    simp only [Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    exact (slotReflection_numerical_commute bob G R S hS h hm P hP r k.val i j).eq
  · exact actual_corner_row_sum bob G R S hS h hm P hP r

/-- Sum a list through the exact finite numerical index, without padding. -/
theorem sum_getD {α : Type} [AddCommMonoid α] (l : List α) (d : ℕ) (h : l.length=d) (fallback : α) :
    (∑ i : Fin d,(l[i.val]?).getD fallback)=l.sum := by
  subst d
  have he := congrArg List.sum (List.ofFn_get l)
  rw [List.sum_ofFn] at he
  calc
    (∑ i : Fin l.length,(l[i.val]?).getD fallback) = ∑ i : Fin l.length,l.get i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [List.getElem?_eq_getElem i.isLt]
      rfl
    _ = l.sum := he
/-- The actual old named effect of the exact restriction. -/
def restrictedNamed (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (i : Fin R.count) : Op :=
  if bob then (RowRestriction.restrict G R S).measurements.bob (R.event i).y (R.event i).b
    else (RowRestriction.restrict G R S).measurements.alice (R.event i).x (R.event i).a

theorem restrictedNamed_support (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (i : Fin R.count) :
    restrictedNamed bob G R S i*P=localOld bob G R S.measurements P i := by
  cases bob
  · have hc := (RowSynchronization.binary_alice (RowRestriction.restrict G R S) (R.event i)
      h hm P hP (RowRestriction.synchronized G R S hS i)).1.1
    change restrictedNamed false G R S i*P=P*restrictedNamed false G R S i at hc
    calc
      _ = P*restrictedNamed false G R S i*P := by rw [← hc,mul_assoc,hP.1.2]
      _ = _ := restriction_alice_effect G R S hS h hm P hP _ _
  · have hc := (RowSynchronization.binary_bob (RowRestriction.restrict G R S) (R.event i)
      h hm P hP (RowRestriction.synchronized G R S hS i)).1.1
    change restrictedNamed true G R S i*P=P*restrictedNamed true G R S i at hc
    calc
      _ = P*restrictedNamed true G R S i*P := by rw [← hc,mul_assoc,hP.1.2]
      _ = _ := restriction_bob_effect G R S hS h hm P hP _ _

theorem slot_eval_support (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) :
    (RowSlots.slot R r j).eval (restrictedNamed bob G R S)*P=slotReflection bob G R S.measurements P r j := by
  have heval : (RowSlots.slot R r j).eval (restrictedNamed bob G R S)=
      sign (RowSlots.slot R r j).negative •
        (match (RowSlots.slot R r j).event with
          | none => (1:Op)
          | some i => (2:ℂ) • restrictedNamed bob G R S i-1) := by
    cases he : (RowSlots.slot R r j).event <;> cases hn : (RowSlots.slot R r j).negative <;>
      simp only [RowSlots.Slot.eval,he,hn,sign,Bool.false_eq_true,ite_false,ite_true,one_smul,neg_one_smul] <;>
      module
  rw [heval,smul_mul_assoc,slotReflection]
  apply congrArg (fun A : Op => sign (RowSlots.slot R r j).negative • A)
  cases he : (RowSlots.slot R r j).event with
  | none => simp only [he,slotEvent,one_mul]; module
  | some i =>
    simp only [he,slotEvent,sub_mul,smul_mul_assoc,one_mul,
      restrictedNamed_support bob G R S hS h hm P hP i]
/-- Each original rational row holds on the supplied original density. -/
theorem supported_row_equation (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) :
    ((R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) • restrictedNamed bob G R S i)*h.op=0 := by
  let A := (R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) • restrictedNamed bob G R S i
  have hs := RowSlots.slots_sum R r (restrictedNamed bob G R S)
  have hz := actual_support_row_sum bob G R S hS h hm P hP r
  have hslot : (∑ j : Fin (RowSlots.dimension R),(RowSlots.slot R r j.val).eval (restrictedNamed bob G R S))=
      ((RowSlots.slots R r).map (RowSlots.Slot.eval (restrictedNamed bob G R S))).sum := by
    have he := sum_getD ((RowSlots.slots R r).map (RowSlots.Slot.eval (restrictedNamed bob G R S)))
      (RowSlots.dimension R) (by rw [List.length_map,RowSlots.slots_length])
      ((⟨none,false⟩ : RowSlots.Slot R.count).eval (restrictedNamed bob G R S))
    simpa only [List.getElem?_map,Option.getD_map,RowSlots.slot] using he
  have hscaled : (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ)) • (A*P)=0 := by
    rw [← smul_mul_assoc]
    change ((2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ)) • A)*P=0
    rw [← hs,← hslot,Finset.sum_mul]
    simp only [slot_eval_support bob G R S hS h hm P hP,hz]
  have hc : (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ))≠0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Nat.ne_of_gt (RowSlots.denominator_pos _))
  have hAP : A*P=0 := (smul_eq_zero.mp hscaled).resolve_left hc
  change A*h.op=0
  rw [← hP.2.1,← mul_assoc,hAP,zero_mul]

#print axioms central_zero_of_corner
#print axioms slotReflection_supported
#print axioms actual_support_row_sum
#print axioms sum_getD
#print axioms restrictedNamed_support
#print axioms slot_eval_support
#print axioms supported_row_equation
end Sigma2.RowScalar