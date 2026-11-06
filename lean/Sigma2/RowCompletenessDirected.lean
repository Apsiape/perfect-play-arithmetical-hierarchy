import Sigma2.RowCompletenessColumnBindings
import Sigma2.RowCompletenessRuleSplit

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns FiniteAncilla TensorLifts

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem pair_question_bound {s} (R : Rows s) (j : ℕ) (hm : Question.pair j ∈ questions R) :
    j<2^(bits R) := by
  have he : j<RowSlots.dimension R := by
    simp [questions] at hm
    have := RowSlots.dimension_pos R
    omega
  simpa only [RowScalar.dimension_bits] using he

theorem slot_question_bound {s} (R : Rows s) (r : Fin R.rowCount) (j : ℕ)
    (hm : Question.slot r j ∈ questions R) : j<2^(bits R) := by
  have he : j<RowSlots.dimension R := by
    simp [questions] at hm
    have := RowSlots.dimension_pos R
    omega
  simpa only [RowScalar.dimension_bits] using he

theorem valid_axis {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) (a : ℕ) :
    valid R (axis R g k) a=decide (a<2) := by
  unfold axis
  split_ifs <;> rfl

theorem operator_zero_event (G : Game) (R : Rows G.scenario) (E F : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (v : AB)
    (hm : ∀ i,left (E i) v=right (F i) v) (q p : Q R) (a b : AA (scenario G R))
    (hz : (newPartition G R E hE q).effect a*(newPartition G R E hE p).effect b=0) :
    (left ((newPartition G R E hE q).effect a)*right ((newPartition G R F hF p).effect b))
      (entangle (RowSlots.dimension R) v)=0 := by
  change left _ (right _ _)=0
  rw [← newPartition_mirror G R E F hE hF v hm p b]
  change (left _*left _) _=0
  rw [← left_mul,hz,CoarseCells.left_zero,zero_apply]

theorem directed_zero (G : Game) (R : Rows G.scenario) (E F : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (v : AB)
    (hm : ∀ i,left (E i) v=right (F i) v)
    (hrow : ∀ r,left (∑ j : Fin (RowSlots.dimension R),(RowSlots.slot R r j.val).eval E) v=0)
    (q p : Q R) (hq : q ∈ questions R) (hp : p ∈ questions R) (a b : AA (scenario G R))
    (hz : directed R q p a.val b.val=false) :
    (left ((newPartition G R E hE q).effect a)*right ((newPartition G R F hF p).effect b))
      (entangle (RowSlots.dimension R) v)=0 := by
  by_contra hn
  have hvq : valid R q a.val=true := by
    cases he : valid R q a.val
    · have hh := newPartition_invalid G R E hE q a he
      simp only [hh,CoarseCells.left_zero,zero_mul,zero_apply] at hn
      exact False.elim (hn trivial)
    · rfl
  have hvp : valid R p b.val=true := by
    cases he : valid R p b.val
    · have hh := newPartition_invalid G R F hF p b he
      simp only [hh,CoarseCells.right_zero,mul_zero,zero_apply] at hn
      exact False.elim (hn trivial)
    · rfl
  have hop : ∀ he : (newPartition G R E hE q).effect a*(newPartition G R E hE p).effect b=0,False :=
    fun he => hn (operator_zero_event G R E F hE hF v hm q p a b he)
  have ht : directed R q p a.val b.val=true := by
    cases q with
    | anchor => rfl
    | cell g x y => rfl
    | line g col k =>
        simp only [directed,List.all_eq_true]
        intro j hj
        by_cases he : p=(if col then Question.cell g j k else Question.cell g k j)
        · rw [if_pos he]
          subst p
          rw [decide_eq_true_eq]
          by_contra hne
          apply hop
          apply line_binding_zero G R E hE g col k j a b
          · exact of_decide_eq_true hvq
          · cases col <;> exact of_decide_eq_true hvp
          · exact hne
        · rw [if_neg he]
    | cross g h k l =>
        by_cases hgh : g=h
        · simp only [directed,hgh,ite_true]
        · simp only [directed,if_neg hgh,Bool.and_eq_true]
          constructor
          · split_ifs with he
            · subst p
              rw [decide_eq_true_eq]
              by_contra hne
              apply hop
              exact cross_binding_first_zero G R E hE g h hgh k l a b
                (by simpa only [valid,if_neg hgh,decide_eq_true_eq] using hvq)
                (by simpa only [valid_axis,decide_eq_true_eq] using hvp) hne
            · rfl
          · split_ifs with he
            · subst p
              rw [decide_eq_true_eq]
              by_contra hne
              apply hop
              exact cross_binding_second_zero G R E hE g h hgh k l a b
                (by simpa only [valid,if_neg hgh,decide_eq_true_eq] using hvq)
                (by simpa only [valid_axis,decide_eq_true_eq] using hvp) hne
            · rfl
    | oldAxis i g k =>
        simp only [directed]
        split_ifs with he
        · subst p
          rw [decide_eq_true_eq]
          by_contra hne
          apply hop
          exact oldAxis_binding_zero G R E hE i g k a b (of_decide_eq_true hvq)
            (by simpa only [valid_axis,decide_eq_true_eq] using hvp) hne
        · rfl
    | global isX =>
        simp only [directed,List.all_eq_true]
        intro g hg k hk
        let ax : Fin 4 := ⟨k.val+if isX then 2 else 0,by split <;> have := k.isLt <;> omega⟩
        change (if p=axis R g ax then decide (b.val=bitAnswer (Nat.testBit a.val (2*g.val+k.val))) else true)=true
        by_cases he : p=axis R g ax
        · rw [if_pos he]
          subst p
          rw [decide_eq_true_eq]
          by_contra hne
          apply hop
          exact global_binding_zero G R E hE isX g k a b (of_decide_eq_true hvq)
            (by simpa only [valid_axis,decide_eq_true_eq] using hvp) hne
        · rw [if_neg he]
    | pair j =>
        have hj := pair_question_bound R j hq
        have ha : a.val<2*RowSlots.dimension R := (of_decide_eq_true hvq).1
        simp only [directed,Bool.and_eq_true]
        constructor
        · split_ifs with he
          · subst p
            rw [decide_eq_true_eq]
            by_contra hne
            apply hop
            exact pair_X_binding_zero G R E hE j hj a b ha (of_decide_eq_true hvp) hne
          · rfl
        · split_ifs with he
          · subst p
            simp only [List.all_eq_true]
            intro ell hell
            split_ifs with hepar
            · rfl
            · rw [decide_eq_true_eq]
              by_contra hne
              apply hop
              exact pair_Z_binding_zero G R E hE j ell hj a b ha (of_decide_eq_true hvp)
                (Bool.eq_false_iff.mpr hepar) hne
          · rfl
    | slot r j =>
        have hj := slot_question_bound R r j hq
        simp only [directed,Bool.and_eq_true]
        constructor
        · split_ifs with he
          · subst p
            rw [decide_eq_true_eq]
            by_contra hne
            apply hop
            exact slot_pair_binding_zero G R E hE r j hj a b (of_decide_eq_true hvq)
              (of_decide_eq_true hvp).1 hne
          · rfl
        · cases he : (RowSlots.slot R r j).event with
          | some i => rfl
          | none =>
              split_ifs with heq
              · subst p
                rw [decide_eq_true_eq]
                by_contra hne
                apply hop
                rw [slot_anchor_binding_zero G R E hE r j hj he a (of_decide_eq_true hvq)
                  (by simpa only [show b.val=1 from of_decide_eq_true hvp] using hne),zero_mul]
              · rfl
    | column r =>
        simp only [directed,Bool.and_eq_true]
        constructor
        · split_ifs with he
          · subst p
            by_cases ha : a.val=0
            · by_cases hb : b.val=0
              · exact False.elim (hn (column_reference_binding_zero G R E F hE hF r v (hrow r) a b ha hb))
              · simp only [ha,hb,decide_false,Bool.and_false,Bool.not_false]
            · simp only [ha,decide_false,Bool.false_and,Bool.not_false]
          · rfl
        · simp only [List.all_eq_true]
          intro j hj
          split_ifs with he hc
          · rfl
          · subst p
            rw [decide_eq_true_eq]
            by_contra hne
            apply hop
            have hjb : j<2^(bits R) := by
              have hjr := List.mem_range.mp (List.mem_of_mem_drop hj)
              simpa only [RowScalar.dimension_bits] using hjr
            exact column_slot_binding_zero G R E hE r j hjb a b (of_decide_eq_true hvq)
              (of_decide_eq_true hvp) hc hne
          · rfl
  rw [hz] at ht
  contradiction

end Sigma2.RowCompleteness
