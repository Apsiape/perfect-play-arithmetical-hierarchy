import Sigma2.RowScalarBob
import Sigma2.RowRestriction

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame TensorLifts Preliminaries CoarseCells FiniteSpectral MirrorAlgebra MirrorUnits

def oldEvent (G : Game) (R : Rows G.scenario) (i : Fin R.count) : NamedEvent (scenario G R) :=
  ⟨(embedding G R).qA (R.event i).x,(embedding G R).qB (R.event i).y,
    (embedding G R).aA (R.event i).a,(embedding G R).aB (R.event i).b⟩

def oldEffect (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P : Op) (i : Fin R.count) : Op :=
  P*M.alice (oldEvent G R i).x (oldEvent G R i).a*P

def oldBobEffect (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P : Op) (i : Fin R.count) : Op :=
  P*M.bob (oldEvent G R i).y (oldEvent G R i).b*P

theorem old_synchronized (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S) (i : Fin R.count) :
    BinaryEventSynchronized S (oldEvent G R i) := by
  intro a b hab
  have hs : oldSync R (R.event i).x (R.event i).y a.val b.val=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hi := (List.all_eq_true.mp hh) i (List.mem_finRange i)
    apply hab
    simpa [oldEvent,embedding,Fin.ext_iff] using hi
  apply rejected_probability G R S hS
  change accepts G R _ _ _ _=false
  simp [oldEvent,accepts,decodeA_old,decodeB_old,hs]

def oldAxisQ {s} (R : Rows s) (i : Fin R.count) (g : Fin (RowSlots.squares R))
    (k : Fin 4) : NewQ R :=
  ⟨.oldAxis i g k,by simp [questions,List.mem_flatMap,List.mem_map]⟩

private theorem old_joint (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (i : Fin R.count) (g : Fin (RowSlots.squares R)) (k : Fin 4) (t : Bool) :
    let A := S.measurements.alice (qa G R (oldAxisQ R i g k))
    let B := S.measurements.bob (oldEvent G R i).y
    let f := fun a : AA (scenario G R) => decide (a.val/2=1)
    let u := fun b : BB (scenario G R) => decide (b=(oldEvent G R i).b)
    left (coarse A f t) S.vector=right (coarse B u t) S.vector ∧
      Projection (coarse (compressed P A) f t) := by
  dsimp only
  have hh := coarse_analysis S h hm P hP
    (S.measurements.alice (qa G R (oldAxisQ R i g k)))
    (S.measurements.bob (oldEvent G R i).y)
    (S.measurements.alice_pos _) (S.measurements.bob_pos _)
    (S.measurements.alice_sum _) (S.measurements.bob_sum _)
    (fun a : AA (scenario G R) => decide (a.val/2=1))
    (fun b : BB (scenario G R) => decide (b=(oldEvent G R i).b)) ?_ t
  · exact ⟨hh.1,by rw [coarse_compressed]; exact hh.2.2.1⟩
  · intro a b hab
    have hz := rejected_probability G R (normalOfPure S) hS
      (qa G R (oldAxisQ R i g k)) (oldEvent G R i).y a b ?_
    · simpa only [normalOfPure_probability,PureStrategy.probability,measurements_left,measurements_right] using hz
    · change accepts G R _ _ _ _=false
      simp only [oldEvent,accepts,decode_qa,decodeB_old,oldAxisQ,bindOldB,ite_true]
      have hn : ¬ (b.val=(R.event i).b.val ↔ a.val/2=1) := by
        intro he
        apply hab
        simp only [oldEvent,embedding,Fin.ext_iff]
        simp only [he]
      simp only [hn,decide_false,Bool.and_false]

private theorem coarse_fine_commute {ι τ : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq τ] (B : ι → Op) (p : ι → τ) (t : τ) (P : Op)
    (hP : Projection P) (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hq : Projection (coarse B p t)) (a : ι) : Commute (coarse B p t) (B a) := by
  have hl := coarse_action B p t P hP hB hs hq a
  have hr := congrArg star hl
  simp only [star_mul,hq.1,(hB a).isSelfAdjoint.star_eq] at hr
  by_cases ha : p a=t
  · simp only [ha,ite_true,(hB a).isSelfAdjoint.star_eq] at hl hr
    exact hl.trans hr.symm
  · simp only [ha,ite_false] at hl hr
    exact hl.trans ((star_zero Op).symm.trans hr.symm)

private theorem coarse_signed_commute {ι τ : Type} [Fintype ι] [DecidableEq ι]
    [DecidableEq τ] (B : ι → Op) (p : ι → τ) (t : τ) (q : ι → Fin 4) (P : Op)
    (hP : Projection P) (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hq : Projection (coarse B p t)) : Commute (coarse B p t) (signed B q) := by
  have hc (u : Fin 4) : Commute (coarse B p t) (coarse B q u) := by
    unfold coarse
    change (∑ a,if p a=t then B a else 0)*(∑ a,if q a=u then B a else 0)=_
    rw [Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : q a=u
    · simpa only [coarse,ha,ite_true] using (coarse_fine_commute B p t P hP hB hs hq a).eq
    · simp only [ha,ite_false,mul_zero,zero_mul]
  exact (hc 1).sub_right (hc 2)

/-- The measured old-axis joint puts each old named projection in the
commutant of every actual scalar axis. -/
theorem pure_old_axis_commute (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (i : Fin R.count) (g : Fin (RowSlots.squares R)) (k : Fin 4) :
    Commute (oldEffect G R S.measurements P i) (binary G R S.measurements P (axisQ R g k)) := by
  let q := oldAxisQ R i g k
  let A := compressed P (S.measurements.alice (qa G R q))
  let f := fun a : AA (scenario G R) => decide (a.val/2=1)
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  have he : coarse A f true=oldEffect G R S.measurements P i := by
    rw [coarse_compressed]
    apply local_eq S h hm P hP _ _ (by simp only [mul_assoc,hP.1.2])
      (by simp only [oldEffect,mul_assoc,hP.1.2])
    have hj := compressed_mirror S.vector P Q _ _ (left_support S h hm P hP)
      (right_support S hB hmB Q hQ) (old_joint G R S hS h hm P hP i g k true).1
    have ho := compressed_mirror S.vector P Q _ _ (left_support S h hm P hP)
      (right_support S hB hmB Q hQ)
      (by simpa only [measurements_left,measurements_right] using
        (RowSynchronization.pure_binary_analysis S (oldEvent G R i) h hm P hP
          (old_synchronized G R (normalOfPure S) hS i)).1)
    have hu : coarse (S.measurements.bob (oldEvent G R i).y)
        (fun b => decide (b=(oldEvent G R i).b)) true=
        S.measurements.bob (oldEvent G R i).y (oldEvent G R i).b := by simp [coarse]
    rw [hu] at hj
    exact hj.trans ho.symm
  have hz (a b : ℕ) (hab : binaryClass (a%2)≠binaryClass b) :
      newRule R q.val (axisQ R g k).val a b=false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    have hd : directed R q.val (axisQ R g k).val a b=true := by
      simp only [newRule,Bool.and_eq_true] at hh
      exact hh.1.2
    have hb : b=a%2 := by simpa only [q,oldAxisQ,axisQ_val,directed,ite_true,decide_eq_true_eq] using hd
    exact hab (congrArg binaryClass hb.symm)
  have ha := bound_signed G R S hS h hm P hP q (axisQ R g k) (fun a => binaryClass (a%2)) hz
  rw [← he,← ha]
  exact coarse_signed_commute A f true _ P hP.1
    (compressed_positive P hP.1 _ (S.measurements.alice_pos _))
    (compressed_sum P hP.1 _ (S.measurements.alice_sum _))
    (old_joint G R S hS h hm P hP i g k true).2

/-- Every actual old named projection centralizes the entire common scalar
matrix algebra, for arbitrary normal strategies. -/
theorem old_units_commute (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (a : Fin R.count) (i j : Register (RowSlots.squares R)) :
    Commute (oldEffect G R S.measurements P a)
      (tensorUnit P (localUnit G R S.measurements P) i j) := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  have hc (g k) := pure_old_axis_commute G R T (pure_perfect_transfer G R S hS T hprob)
    h (hM h hm) P hP a g k
  have hc' (g k) : Commute (oldEffect G R S.measurements P a)
      (binary G R S.measurements P (axisQ R g k)) := by
    simpa only [oldEffect,binary,hA] using hc g k
  have hp : Commute (oldEffect G R S.measurements P a) P := by
    change (P*_*P)*P=P*(P*_*P)
    calc
      _ = oldEffect G R S.measurements P a := by
        simp only [oldEffect,mul_assoc,hP.1.2]
      _ = _ := by simp only [oldEffect,← mul_assoc,hP.1.2]
  suffices ∀ {n} (U : Fin n → FourUnits.Index → FourUnits.Index → Op),
      (∀ g i j,Commute (oldEffect G R S.measurements P a) (U g i j)) →
      ∀ i j : Register n,Commute (oldEffect G R S.measurements P a) (tensorUnit P U i j) from
    this _ (fun g => commute_localUnit G R S.measurements P _ g hp (hc' g)) i j
  intro n U hU i j
  induction n with
  | zero => exact hp
  | succ n ih => exact (hU 0 i.1 j.1).mul_right (ih _ (fun g => hU g.succ) i.2 j.2)

#print axioms old_synchronized
#print axioms pure_old_axis_commute
#print axioms old_units_commute

/-- Old named projections are the actual support-compressions, hence sharp. -/
theorem old_projection (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P) (i : Fin R.count) :
    Projection (oldEffect G R S.measurements P i) :=
  (RowSynchronization.binary_alice S (oldEvent G R i) h hm P hP
    (old_synchronized G R S hS i)).1.2

theorem old_bob_projection (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q) (i : Fin R.count) :
    Projection (oldBobEffect G R S.measurements Q i) :=
  (RowSynchronization.binary_bob S (oldEvent G R i) h hm Q hQ
    (old_synchronized G R S hS i)).1.2

private theorem pure_old_bob_units_commute (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (hA hB : Density) (hmA : MarginalA (normalOfPure S) hA)
    (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q)
    (a : Fin R.count) (i j : Register (RowSlots.squares R)) :
    Commute (oldBobEffect G R S.measurements Q a) (bobTensor G R S.measurements Q i j) := by
  let E := oldEffect G R S.measurements P a
  let F := oldBobEffect G R S.measurements Q a
  let t := tensorUnit P (localUnit G R S.measurements P)
  let u := bobTensor G R S.measurements Q
  have hc := old_units_commute G R (normalOfPure S) hS hA hmA P hP a j i
  change E*t j i=t j i*E at hc
  have hm := common_units_mirror G R S hS hA hB hmA hmB P Q hP hQ j i
  have he : left E S.vector=right F S.vector :=
    compressed_mirror S.vector P Q _ _ (left_support S hA hmA P hP)
      (right_support S hB hmB Q hQ)
      (by simpa only [measurements_left,measurements_right] using
        (RowSynchronization.pure_binary_analysis S (oldEvent G R a) hA hmA P hP
          (old_synchronized G R (normalOfPure S) hS a)).1)
  change F*u i j=u i j*F
  apply right_local_eq S hB hmB Q hQ _ _
    (by dsimp [F,oldBobEffect]; rw [mul_assoc,(bobTensor_supported G R S.measurements Q hQ.1 i j).2])
    (by dsimp [F,oldBobEffect]; simp only [mul_assoc,hQ.1.2])
  have h1 := mirror_mul S.vector E (t j i) F (u i j) he hm.1
  have h2 := mirror_mul S.vector (t j i) E (u i j) F hm.1 he
  rw [hc] at h1
  exact h2.symm.trans h1

/-- Old named projections lie in the same scalar commutant on Bob's actual
normal support, with the transposed scalar-unit convention. -/
theorem old_bob_units_commute (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q)
    (a : Fin R.count) (i j : Register (RowSlots.squares R)) :
    Commute (oldBobEffect G R S.measurements Q a) (bobTensor G R S.measurements Q i j) := by
  obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
  obtain ⟨hA,_,hmA,_⟩ := marginals_exist (normalOfPure T)
  obtain ⟨P,hP⟩ := support_exists hA
  have hh := pure_old_bob_units_commute G R T (pure_perfect_transfer G R S hS T hprob)
    hA h hmA (hM h hm) P Q hP hQ a i j
  have hl : bobLocal G R T.measurements Q=bobLocal G R S.measurements Q := by
    funext g i j
    simp only [bobLocal,bobBinary,hB,Purification.measurements,TensorLifts.measurements]
  simp only [bobTensor,hl] at hh
  simpa only [oldBobEffect,bobTensor,hB,Purification.measurements,TensorLifts.measurements] using hh

#print axioms old_projection
#print axioms old_bob_projection
#print axioms old_bob_units_commute
#print axioms old_joint
#print axioms coarse_fine_commute
#print axioms coarse_signed_commute
#print axioms pure_old_bob_units_commute

end Sigma2.RowScalar