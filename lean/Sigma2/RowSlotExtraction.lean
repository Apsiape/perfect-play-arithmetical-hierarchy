import Sigma2.RowSlotGraphs

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral

/-- The sign label used verbatim by the actual column/slot rule; class 2 is
the spectator sector and belongs to neither active graph. -/
def slotGraphLabel {s} (R : Rows s) (r : Fin R.rowCount) (j : ℕ)
    (eps : Bool) (a : ℕ) : Bool :=
  decide (a%3≠2 ∧ Bool.xor (decide (a%3=1))
    (Bool.xor (decide (a/3=0)) (RowSlots.slot R r j).negative)=eps)

private theorem graph_answer_iff (neg eps : Bool) (a : ℕ) (ha : a<6) :
    (a%3≠2 ∧ Bool.xor (decide (a%3=1)) (Bool.xor (decide (a/3=0)) neg)=eps) ↔
      a=3+boolNat (Bool.xor eps neg) ∨ a=boolNat (Bool.xor eps (!neg)) := by
  interval_cases a <;> cases neg <;> cases eps <;> decide

theorem new_coarse_sharp (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (q : NewQ R) (f : ℕ → Bool) (t : Bool) :
    Projection (coarse (newEffects bob G R S.measurements P q) (fun a => f a.val) t) := by
  exact (new_coarse_eq bob G R S hS h hm P hP q q f f (by
    intro a b hab
    apply Bool.eq_false_iff.mpr
    intro he
    have heq : a=b := by
      simp only [newRule,Bool.and_eq_true,ite_true,decide_eq_true_eq] at he
      exact he.1.1.2
    exact hab (by rw [heq])) t).2

/-- The two computed graph outcomes are exactly the coarse events read by
the table, with every invalid/padded slot answer removed by perfection. -/
theorem slot_graph_coarse (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool) :
    coarse (newEffects bob G R S.measurements P (slotQ R r j hj))
      (fun a => slotGraphLabel R r j eps a.val) true=
      slotGraph bob G R S.measurements P r j hj eps := by
  let neg := (RowSlots.slot R r j).negative
  let a1 := sixAnswer G R ⟨3+boolNat (Bool.xor eps neg),by have := boolNat_lt (Bool.xor eps neg); omega⟩
  let a0 := sixAnswer G R ⟨boolNat (Bool.xor eps (!neg)),by have := boolNat_lt (Bool.xor eps (!neg)); omega⟩
  let B := newEffects bob G R S.measurements P (slotQ R r j hj)
  have hne : a1≠a0 := by
    intro he
    have hv := congrArg Fin.val he
    have hb := boolNat_lt (Bool.xor eps (!neg))
    change 3+boolNat (Bool.xor eps neg)=boolNat (Bool.xor eps (!neg)) at hv
    omega
  have hind (b : Answer G R) :
      (if slotGraphLabel R r j eps b.val=true then B b else 0)=
        (if b=a1 then B b else 0)+(if b=a0 then B b else 0) := by
    by_cases hb : b.val<6
    · have he : slotGraphLabel R r j eps b.val=true ↔ b=a1 ∨ b=a0 := by
        simp only [slotGraphLabel,decide_eq_true_eq,graph_answer_iff _ _ _ hb]
        simp only [Fin.ext_iff,a1,a0,sixAnswer,neg]
      simp only [he]
      by_cases h1 : b=a1
      · have h0 : b≠a0 := by intro hh; exact hne (h1.symm.trans hh)
        rw [if_pos (Or.inl h1),if_pos h1,if_neg h0,add_zero]
      · by_cases h0 : b=a0
        · rw [if_pos (Or.inr h0),if_neg h1,if_pos h0,zero_add]
        · rw [if_neg (not_or.mpr ⟨h1,h0⟩),if_neg h1,if_neg h0,add_zero]
    · have hz : B b=0 := new_invalid_zero bob G R S hS h hm P hP _ b (by simp [slotQ,valid,hb])
      simp only [hz,ite_self,add_zero]
  change (∑ b,if slotGraphLabel R r j eps b.val=true then B b else 0)=B a1+B a0
  simp_rw [hind]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem slot_graph_projection (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool) :
    Projection (slotGraph bob G R S.measurements P r j hj eps) := by
  rw [← slot_graph_coarse bob G R S hS h hm P hP]
  exact new_coarse_sharp bob G R S hS h hm P hP _ _ true

/-- All forbidden active graph pairs, including deterministic positive and
negative anchor slots, are actual rejections of the unchanged game table. -/
theorem column_slot_forbidden {s} (R : Rows s) (r : Fin R.rowCount) (j : ℕ)
    (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool) (a b : ℕ)
    (hb : slotGraphLabel R r j eps b=true)
    (hne : eps≠parity (2*RowSlots.squares R) a j) :
    newRule R (.column r) (.slot r j) a b=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hd : directed R (.column r) (.slot r j) a b=true := by
    simp only [newRule,Bool.and_eq_true] at hh
    exact hh.1.2
  have hmj : j ∈ (List.range (RowSlots.dimension R)).drop 1 := by
    rw [List.mem_iff_getElem]
    refine ⟨j-1,by simp; omega,?_⟩
    simp; omega
  simp only [slotGraphLabel,decide_eq_true_eq] at hb
  have hr := (List.all_eq_true.mp (show
      ((List.range (RowSlots.dimension R)).drop 1).all (fun k =>
        if (.slot r j : Q R)=.slot r k then
          if b%3=2 then true else
            decide (Bool.xor (decide (b%3=1))
              (Bool.xor (decide (b/3=0)) (RowSlots.slot R r k).negative)=
                parity (2*RowSlots.squares R) a k) else true)=true from by
                  simpa [directed] using hd)) j hmj
  have he : Bool.xor (decide (b%3=1))
      (Bool.xor (decide (b/3=0)) (RowSlots.slot R r j).negative)=parity (2*RowSlots.squares R) a j := by
    simpa only [ite_true,hb.1,ite_false,decide_eq_true_eq] using hr
  exact hne (hb.2.symm.trans he)

/-- The signed graph formulas in the same actual two-sided support coordinates
already supplied in steps 1 and 2. -/
theorem slot_graph_coordinates (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool) :
    let hu := supportUnits_laws bob G R S hS h hm P hP
    let o := zeroRegister (RowSlots.squares R)
    let F0 := pairJoint bob G R S.measurements P j 0
    let F1 := pairJoint bob G R S.measurements P j 1
    coordinateAction hu o (slotGraph bob G R S.measurements P r j hj eps)=
      coordinateAction hu o ((1/2:ℂ) • ((F0+F1)+RowColumns.sign eps •
        (slotReflection bob G R S.measurements P r j*(F0-F1)))) := by
  rw [slot_graph_formula bob G R S hS h hm P hP]

#print axioms graph_answer_iff
#print axioms new_coarse_sharp
#print axioms slot_graph_coarse
#print axioms slot_graph_projection
#print axioms column_slot_forbidden
#print axioms slot_graph_coordinates
end Sigma2.RowScalar


