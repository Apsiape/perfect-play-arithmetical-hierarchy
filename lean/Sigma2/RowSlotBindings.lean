import Sigma2.RowSpectralCoordinates

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral FiniteJoint TensorLifts MirrorAlgebra

def slotQ {s} (R : Rows s) (r : Fin R.rowCount) (j : ℕ)
    (hj : 0<j ∧ j<RowSlots.dimension R) : NewQ R :=
  ⟨.slot r j,by
    have hjm : j ∈ (List.range (RowSlots.dimension R)).drop 1 := by
      rw [List.mem_iff_getElem]
      refine ⟨j-1,by simp; omega,?_⟩
      simp; omega
    simp only [questions,List.mem_append,List.mem_flatMap,List.mem_map]
    exact Or.inl (Or.inr ⟨r,List.mem_finRange r,j,hjm,rfl⟩)⟩

/-- The old binary projection on the selected party's original support. -/
def localOld (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (i : Fin R.count) : Op :=
  if bob then oldBobEffect G R M P i else oldEffect G R M P i

def slotEvent (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (r : Fin R.rowCount) (j : ℕ) : Op :=
  match (RowSlots.slot R r j).event with
  | none => P
  | some i => localOld bob G R M P i

private theorem pure_bound_old {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (e : NamedEvent s) (hs : BinaryEventSynchronized (normalOfPure S) e)
    (x : QA s) (f : ℕ → Bool)
    (hz : ∀ a b,f a.val≠decide (b=e.b) → S.probability x e.y a b=0) :
    coarse (compressed P (S.measurements.alice x)) (fun a => f a.val) true=
      P*S.measurements.alice e.x e.a*P := by
  have hh := coarse_analysis S h hm P hP
    (S.measurements.alice x) (S.measurements.bob e.y)
    (S.measurements.alice_pos _) (S.measurements.bob_pos _)
    (S.measurements.alice_sum _) (S.measurements.bob_sum _)
    (fun a => f a.val) (fun b => decide (b=e.b))
    (fun a b hab => by simpa only [PureStrategy.probability,measurements_left,measurements_right] using hz a b hab) true
  have ho := (RowSynchronization.pure_binary_analysis S e h hm P hP hs).1
  have he : coarse (S.measurements.bob e.y) (fun b => decide (b=e.b)) true=
      S.measurements.bob e.y e.b := by simp [coarse]
  rw [he] at hh
  rw [coarse_compressed]
  apply local_eq S h hm P hP _ _ (by simp [mul_assoc,hP.1.2]) (by simp [mul_assoc,hP.1.2])
  have ha := compressed_mirror S.vector P 1 _ _ (left_support S h hm P hP) (by simp [right_one]) hh.1
  have hb := compressed_mirror S.vector P 1 _ _ (left_support S h hm P hP) (by simp [right_one])
    (by simpa only [measurements_left,measurements_right] using ho)
  exact ha.trans hb.symm

/-- Actual old-event binding, with Bob treated on his own original support. -/
theorem slot_old_true (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R)
    (i : Fin R.count) (hi : (RowSlots.slot R r j).event=some i) :
    coarse (newEffects bob G R S.measurements P (slotQ R r j hj))
      (fun a => decide (a.val/3=1)) true=localOld bob G R S.measurements P i := by
  cases bob
  · obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
    have hs := old_synchronized G R (normalOfPure T) (pure_perfect_transfer G R S hS T hprob) i
    have hh := pure_bound_old T h (hM h hm) P hP (oldEvent G R i) hs
      (qa G R (slotQ R r j hj)) (fun a => decide (a/3=1)) (by
        intro a b hab
        rw [← hprob]
        apply rejected_probability G R S hS
        change accepts G R _ _ _ _=false
        have hn : ¬ (b.val=(R.event i).b.val ↔ a.val/3=1) := by
          intro he
          apply hab
          simp only [oldEvent,embedding,Fin.ext_iff]
          simp only [he]
        simp [accepts,decode_qa,decodeB_old,slotQ,oldEvent,bindOldB,hi,hn])
    simpa [newEffects,localOld,oldEffect,hA] using hh
  · obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
    let W := PureTransfer.flipPure T
    let e : NamedEvent (PureTransfer.flipScenario (scenario G R)) :=
      ⟨(oldEvent G R i).y,(oldEvent G R i).x,(oldEvent G R i).b,(oldEvent G R i).a⟩
    have hs : BinaryEventSynchronized (normalOfPure W) e := by
      intro b a hab
      rw [normalOfPure_probability,PureTransfer.flipPure_probability,← hprob]
      exact old_synchronized G R S hS i a b (fun he => hab he.symm)
    have hh := pure_bound_old W h (hM h hm) P hP e hs
      (qb G R (slotQ R r j hj)) (fun a => decide (a/3=1)) (by
        intro b a hab
        rw [PureTransfer.flipPure_probability,← hprob]
        apply rejected_probability G R S hS
        change accepts G R _ _ _ _=false
        have hn : ¬ (a.val=(R.event i).a.val ↔ b.val/3=1) := by
          intro he
          apply hab
          simp only [e,oldEvent,embedding,Fin.ext_iff]
          simp only [he]
        simp [accepts,decode_qb,decodeA_old,slotQ,e,oldEvent,bindOldA,hi,hn])
    simpa [newEffects,localOld,oldBobEffect,e,W,PureTransfer.flipPure,
      PureTransfer.flipMeasurements,Purification.measurements,TensorLifts.measurements,hB,
      Answer,AA,BB,scenario,PureTransfer.flipScenario] using hh

/-- Deterministic slots are bound to the actual deterministic anchor, including
when the old game has no questions that name any event. -/
theorem slot_anchor_true (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R)
    (hi : (RowSlots.slot R r j).event=none) :
    coarse (newEffects bob G R S.measurements P (slotQ R r j hj))
      (fun a => decide (a.val/3=1)) true=P := by
  let q : NewQ R := ⟨.anchor,by simp [questions]⟩
  have hc := new_coarse_eq bob G R S hS h hm P hP (slotQ R r j hj) q
    (fun a => decide (a/3=1)) (fun b => decide (b=1)) (by
      intro a b hab
      apply Bool.eq_false_iff.mpr
      intro he
      have hd : directed R (.slot r j) .anchor a b=true := by
        simp only [newRule,Bool.and_eq_true] at he
        exact he.1.2
      have heq : a/3=b := by simpa [directed,hi] using hd
      exact hab (by rw [heq])) true
  rw [hc.1]
  have hz (a : Answer G R) (ha : a.val≠1) : newEffects bob G R S.measurements P q a=0 :=
    new_invalid_zero bob G R S hS h hm P hP q a (by simp [q,valid,ha])
  conv_rhs => rw [← new_sum bob G R S.measurements P hP.1 q]
  unfold coarse
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a.val=1
  · simp [ha]
  · simp [ha,hz a ha]

/-- Both binary old-event marginals of every actual six-answer slot. -/
theorem slot_event_marginal (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (t : Bool) :
    coarse (newEffects bob G R S.measurements P (slotQ R r j hj))
      (fun a => decide (a.val/3=1)) t=
      if t then slotEvent bob G R S.measurements P r j else P-slotEvent bob G R S.measurements P r j := by
  have ht : coarse (newEffects bob G R S.measurements P (slotQ R r j hj))
      (fun a => decide (a.val/3=1)) true=slotEvent bob G R S.measurements P r j := by
    cases hi : (RowSlots.slot R r j).event with
    | none => simpa only [slotEvent,hi] using slot_anchor_true bob G R S hS h hm P hP r j hj hi
    | some i => simpa only [slotEvent,hi] using slot_old_true bob G R S hS h hm P hP r j hj i hi
  cases t
  · have hs := (coarse_sum (newEffects bob G R S.measurements P (slotQ R r j hj))
        (fun a => decide (a.val/3=1))).trans (new_sum bob G R S.measurements P hP.1 _)
    simp only [Fintype.sum_bool,ht] at hs
    simp only [Bool.false_eq_true,ite_false]
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hs)
  · exact ht

#print axioms pure_bound_old
#print axioms slot_old_true
#print axioms slot_anchor_true
#print axioms slot_event_marginal
end Sigma2.RowScalar

