import Sigma2.RowSlotLaws
import Sigma2.RowWalsh

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral TensorLifts MirrorAlgebra

private theorem pure_forbidden_product {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x z : QA s) (y : QB s) (p : ℕ → Bool) (a : AA s) (t : Bool)
    (hdiag : ∀ c b,p c.val≠p b.val → S.probability z y c b=0)
    (hz : ∀ b,p b.val=t → S.probability x y a b=0) :
    compressed P (S.measurements.alice x) a*
      coarse (compressed P (S.measurements.alice z)) (fun b => p b.val) t=0 := by
  let A := S.measurements.alice x a
  let E := coarse (S.measurements.alice z) (fun b => p b.val) t
  let F := coarse (S.measurements.bob y) (fun b => p b.val) t
  have hs := left_support S h hm P hP
  have han := coarse_analysis S h hm P hP
    (S.measurements.alice z) (S.measurements.bob y)
    (S.measurements.alice_pos z) (S.measurements.bob_pos y)
    (S.measurements.alice_sum z) (S.measurements.bob_sum y)
    (fun b => p b.val) (fun b => p b.val)
    (fun c b hcb => by simpa only [PureStrategy.probability,measurements_left,measurements_right] using hdiag c b hcb) t
  have hmirror : left (P*E*P) S.vector=right F S.vector := by
    have hc := compressed_mirror S.vector P 1 E F hs (by simp [right_one]) han.1
    simpa only [one_mul,mul_one] using hc
  have hzero : (left A*right F) S.vector=0 := by
    dsimp [F]
    unfold coarse
    rw [right_sum,Finset.mul_sum,sum_apply]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : p b.val=t
    · rw [ite_eq_left hb]
      apply positive_apply_eq_zero _ (joint_positive A _ (S.measurements.alice_pos x a) (S.measurements.bob_pos y b))
      simpa only [PureStrategy.probability,measurements_left,measurements_right] using hz b hb
    · simp [hb]
  rw [coarse_compressed]
  apply local_eq S h hm P hP _ 0
    (by simp only [compressed,mul_assoc,hP.1.2]) (by simp)
  rw [left_zero]
  change left ((P*A*P)*(P*E*P)) S.vector=0
  rw [left_mul]
  change left (P*A*P) (left (P*E*P) S.vector)=0
  rw [hmirror]
  have hp : left P (right F S.vector)=right F S.vector := by
    have hc := congrArg (fun T : BipOp => T S.vector) (commute P F)
    change left P (right F S.vector)=right F (left P S.vector) at hc
    rw [hc,hs]
  simp only [left_mul]
  change left P (left A (left P (right F S.vector)))=0
  rw [hp]
  change left P ((left A*right F) S.vector)=0
  rw [hzero,map_zero]

/-- Any actual forbidden fine/coarse pair gives a same-party product zero
on either original support. Only synchronization of the second question is used. -/
theorem new_forbidden_product (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (q p : NewQ R) (a : Answer G R) (f : ℕ → Bool) (t : Bool)
    (hz : ∀ b,f b=t → newRule R q.val p.val a.val b=false) :
    newEffects bob G R S.measurements P q a*
      coarse (newEffects bob G R S.measurements P p) (fun b => f b.val) t=0 := by
  have hd (c b : ℕ) (hne : f c≠f b) : newRule R p.val p.val c b=false := by
    apply Bool.eq_false_iff.mpr
    intro he
    have heq : c=b := by
      simp only [newRule,Bool.and_eq_true,ite_true,decide_eq_true_eq] at he
      exact he.1.1.2
    exact hne (congrArg f heq)
  cases bob
  · obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
    have hp (x z : NewQ R) (a b : Answer G R) (hab : newRule R x.val z.val a.val b.val=false) :
        T.probability (qa G R x) (qb G R z) a b=0 := by
      rw [← hprob]
      apply rejected_probability G R S hS
      change accepts G R _ _ _ _=false
      simpa only [accepts,decode_qa,decode_qb] using hab
    have hh := pure_forbidden_product T h (hM h hm) P hP
      (qa G R q) (qa G R p) (qb G R p) f a t
      (fun c b hcb => hp p p c b (hd c.val b.val hcb))
      (fun b hb => hp q p a b (hz b.val hb))
    simpa only [newEffects,Bool.false_eq_true,ite_false,hA] using hh
  · obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
    let W := PureTransfer.flipPure T
    have hp (x z : NewQ R) (a b : Answer G R) (hab : newRule R x.val z.val a.val b.val=false) :
        W.probability (qb G R x) (qa G R z) a b=0 := by
      rw [PureTransfer.flipPure_probability,← hprob]
      apply rejected_probability G R S hS
      change accepts G R _ _ _ _=false
      simp only [accepts,decode_qa,decode_qb]
      rw [newRule_comm]
      exact hab
    have hh := pure_forbidden_product W h (hM h hm) P hP
      (qb G R q) (qb G R p) (qa G R p) f a t
      (fun c b hcb => hp p p c b (hd c.val b.val hcb))
      (fun b hb => hp q p a b (hz b.val hb))
    simpa [newEffects,Bool.true_eq,ite_true,W,PureTransfer.flipPure,
      PureTransfer.flipMeasurements,Purification.measurements,TensorLifts.measurements,hB,Answer,AA,BB,scenario,PureTransfer.flipScenario] using hh

def columnQ {s} (R : Rows s) (r : Fin R.rowCount) : NewQ R :=
  ⟨.column r,by simp [questions,List.mem_map]⟩

/-- The actual synchronized column effect is orthogonal to every forbidden
active graph event, on Alice's and Bob's own original supports. -/
theorem column_graph_zero (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a : Answer G R) (j : ℕ)
    (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool)
    (hne : eps≠parity (2*RowSlots.squares R) a.val j) :
    newEffects bob G R S.measurements P (columnQ R r) a*
      slotGraph bob G R S.measurements P r j hj eps=0 := by
  rw [← slot_graph_coarse bob G R S hS h hm P hP]
  exact new_forbidden_product bob G R S hS h hm P hP (columnQ R r)
    (slotQ R r j hj) a (slotGraphLabel R r j eps) true
    (fun b hb => column_slot_forbidden R r j hj eps a.val b hb hne)

theorem new_fine_projection (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (q : NewQ R) (a : Answer G R) :
    Projection (newEffects bob G R S.measurements P q a) := by
  have hh := new_coarse_sharp bob G R S hS h hm P hP q (fun b => decide (b=a.val)) true
  simpa only [coarse,decide_eq_true_eq,← Fin.ext_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh

/-- Both orders of each actual forbidden graph product vanish. -/
theorem graph_column_zero (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a : Answer G R) (j : ℕ)
    (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool)
    (hne : eps≠parity (2*RowSlots.squares R) a.val j) :
    slotGraph bob G R S.measurements P r j hj eps*
      newEffects bob G R S.measurements P (columnQ R r) a=0 := by
  have hh := congrArg star (column_graph_zero bob G R S hS h hm P hP r a j hj eps hne)
  rw [star_mul,(new_fine_projection bob G R S hS h hm P hP _ _).1,
    (slot_graph_projection bob G R S hS h hm P hP r j hj eps).1] at hh
  exact hh.trans (star_zero Op)

/-- Actual forbidden pairs impose the signed two-coordinate graph equation
on every column outcome, before any column-identification assumption. -/
theorem column_graph_equation (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a : Answer G R) (j : ℕ)
    (hj : 0<j ∧ j<RowSlots.dimension R) :
    let C := newEffects bob G R S.measurements P (columnQ R r) a
    let F0 := pairJoint bob G R S.measurements P j 0
    let F1 := pairJoint bob G R S.measurements P j 1
    C*(F0+F1)=RowColumns.sign (parity (2*RowSlots.squares R) a.val j) •
      (C*(slotReflection bob G R S.measurements P r j*(F0-F1))) := by
  dsimp only
  let bit := parity (2*RowSlots.squares R) a.val j
  have hne : (!bit)≠bit := by cases bit <;> decide
  have hz := column_graph_zero bob G R S hS h hm P hP r a j hj (!bit) hne
  rw [slot_graph_formula bob G R S hS h hm P hP] at hz
  rw [mul_smul_comm] at hz
  have hh := congrArg (fun A : Op => (2:ℂ) • A) hz
  simp only [smul_smul,show (2:ℂ)*(1/2)=1 by norm_num,one_smul] at hh
  have hs : RowColumns.sign (!bit)= -RowColumns.sign bit := by cases bit <;> norm_num [RowColumns.sign]
  rw [mul_add,mul_smul_comm,hs] at hh
  apply sub_eq_zero.mp
  calc
    _ = _ := by module
    _ = (2:ℂ) • (0:Op) := hh
    _ = 0 := by module

def zeroAnswer (G : Game) (R : Rows G.scenario) : Answer G R := ⟨0,by simp [scenario]⟩

/-- The final table rejection, before geometric interpretation. -/
theorem column_reference_forbidden {s} (R : Rows s) (r : Fin R.rowCount) :
    newRule R (.column r) (.global true) 0 0=false := by
  simp [newRule,directed]

/-- Actual column-zero/reference orthogonality holds on both supplied normal
supports. The reference is the actual synchronized Global_X zero effect. -/
theorem column_reference_zero (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) :
    newEffects bob G R S.measurements P (columnQ R r) (zeroAnswer G R)*
      newEffects bob G R S.measurements P (globalQ R true) (zeroAnswer G R)=0 := by
  have hh := new_forbidden_product bob G R S hS h hm P hP (columnQ R r)
    (globalQ R true) (zeroAnswer G R) (fun b => decide (b=0)) true (by
      intro b hb
      have hb0 : b=0 := by simpa only [decide_eq_true_eq] using hb
      subst b
      exact column_reference_forbidden R r)
  simpa only [coarse,decide_eq_true_eq,show (0:ℕ)=(zeroAnswer G R).val from rfl,
    ← Fin.ext_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true] using hh

#print axioms pure_forbidden_product
#print axioms new_forbidden_product
#print axioms column_graph_zero
#print axioms new_fine_projection
#print axioms graph_column_zero
#print axioms column_graph_equation
#print axioms column_reference_forbidden
#print axioms column_reference_zero
end Sigma2.RowScalar
