import Sigma2.RowCompletenessOldRules

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns FiniteAncilla TensorLifts

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem decoded_question_mem {s} (R : Rows s) (n : ℕ) :
    ((questions R)[n]?.getD .anchor) ∈ questions R := by
  cases he : (questions R)[n]? with
  | none => simp only [he,Option.getD_none]; simp [questions]
  | some q =>
      simp only [he,Option.getD_some]
      exact List.mem_of_getElem? he

theorem decodeA_mem (G : Game) (R : Rows G.scenario) (x : QA (scenario G R)) (q : Q R)
    (he : decodeA G R x=.inr q) : q ∈ questions R := by
  unfold decodeA at he
  split at he
  · contradiction
  · cases he
    exact decoded_question_mem R _

theorem decodeB_mem (G : Game) (R : Rows G.scenario) (y : QB (scenario G R)) (q : Q R)
    (he : decodeB G R y=.inr q) : q ∈ questions R := by
  unfold decodeB at he
  split at he
  · contradiction
  · cases he
    exact decoded_question_mem R _

theorem honest_A_effect (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i))
    (x : QA (scenario G R)) (a : AA (scenario G R)) :
    (honestMeasurements G R M E F hE hF).alice x a=
      match decodeA G R x with
      | .inl ox => (paddedAlice G R M ox).effect a
      | .inr q => (newPartition G R E hE q).effect a := by
  change (match decodeA G R x with
    | .inl ox => paddedAlice G R M ox
    | .inr q => (newPartition G R E hE q).toPOVM).effect a=_
  cases decodeA G R x <;> rfl

theorem honest_B_effect (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i))
    (y : QB (scenario G R)) (b : BB (scenario G R)) :
    (honestMeasurements G R M E F hE hF).bob y b=
      match decodeB G R y with
      | .inl oy => (paddedBob G R M oy).effect b
      | .inr q => (newPartition G R F hF q).effect b := by
  change (match decodeB G R y with
    | .inl oy => paddedBob G R M oy
    | .inr q => (newPartition G R F hF q).toPOVM).effect b=_
  cases decodeB G R y <;> rfl

theorem paddedAlice_valid (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (x : QA G.scenario) (a : AA (scenario G R)) (ha : a.val<G.scenario.answersA+1) :
    (paddedAlice G R M x).effect a=amplify (RowSlots.dimension R) (M.alice x ⟨a.val,ha⟩) := by
  have he : a=(embedding G R).aA ⟨a.val,ha⟩ := Fin.ext rfl
  exact (congrArg (paddedAlice G R M x).effect he).trans
    (POVM.coarse_injective _ _ (embedding G R).iaA _)

theorem paddedBob_valid (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (y : QB G.scenario) (b : BB (scenario G R)) (hb : b.val<G.scenario.answersB+1) :
    (paddedBob G R M y).effect b=amplify (RowSlots.dimension R) (M.bob y ⟨b.val,hb⟩) := by
  have he : b=(embedding G R).aB ⟨b.val,hb⟩ := Fin.ext rfl
  exact (congrArg (paddedBob G R M y).effect he).trans
    (POVM.coarse_injective _ _ (embedding G R).iaB _)

theorem honest_rejection_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hS : Perfect G S) (hR : RowsHold R S) (hN : NamedBinaryProjections R S)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i))
    (he : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (hf : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k))
    (hm : ∀ i k,0<S.weight k → left (E i) (S.vector k)=right (F i) (S.vector k))
    (x : QA (scenario G R)) (y : QB (scenario G R))
    (a : AA (scenario G R)) (b : BB (scenario G R)) (hz : (game G R).accepts x y a b=false) (k : ℕ) (hk : 0<S.weight k) :
    ((honestMeasurements G R S.measurements E F hE hF).left x a*
      (honestMeasurements G R S.measurements E F hE hF).right y b)
        (entangle (RowSlots.dimension R) (S.vector k))=0 := by
  have hEA : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k) :=
    fun i k hk => (hm i k hk).trans (hf i k hk)
  have hFB : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k) :=
    fun i k hk => (hm i k hk).symm.trans (he i k hk)
  change accepts G R x y a b=false at hz
  rw [measurements_left,measurements_right,honest_A_effect,honest_B_effect]
  cases hxa : decodeA G R x with
  | inl ox =>
      cases hyb : decodeB G R y with
      | inl oy =>
          simp only [hxa,hyb]
          simp only [accepts,hxa,hyb] at hz
          by_cases ha : a.val<G.scenario.answersA+1
          · by_cases hb : b.val<G.scenario.answersB+1
            · rw [paddedAlice_valid G R S.measurements ox a ha,paddedBob_valid G R S.measurements oy b hb]
              apply amplified_event_zero
              have hp := old_rule_zero G R S hS hN ox oy ⟨a.val,ha⟩ ⟨b.val,hb⟩
                (by simpa only [dif_pos ha,dif_pos hb] using hz)
              simpa only [measurements_left,measurements_right] using component_event_zero S _ _ _ _ hp k hk
            · rw [paddedBob_invalid G R S.measurements oy b (by omega),CoarseCells.right_zero,mul_zero,zero_apply]
          · rw [paddedAlice_invalid G R S.measurements ox a (by omega),CoarseCells.left_zero,zero_mul,zero_apply]
      | inr p =>
          simp only [hxa,hyb]
          simp only [accepts,hxa,hyb] at hz
          by_cases ha : a.val<G.scenario.answersA+1
          · cases hv : valid R p b.val
            · rw [newPartition_invalid G R F hF p b hv,CoarseCells.right_zero,mul_zero,zero_apply]
            · rw [paddedAlice_valid G R S.measurements ox a ha]
              have hb : bindOldA R ox p a.val b.val=false := by simpa only [ha,decide_true,hv,Bool.true_and] using hz
              cases p with
              | oldAxis i g l => exact oldAxis_A_zero G R S hN F hF hFB hf i g l ox ⟨a.val,ha⟩ b (of_decide_eq_true hv) hb k hk
              | slot r j => exact slot_A_zero G R S hN F hF hFB hf r j (slot_question_bound R r j (decodeB_mem G R y _ hyb)) ox ⟨a.val,ha⟩ b (of_decide_eq_true hv) hb k hk
              | anchor => simp only [bindOldA] at hb; contradiction
              | cell g xx yy => simp only [bindOldA] at hb; contradiction
              | line g col l => simp only [bindOldA] at hb; contradiction
              | cross g h l m => simp only [bindOldA] at hb; contradiction
              | global isX => simp only [bindOldA] at hb; contradiction
              | pair j => simp only [bindOldA] at hb; contradiction
              | column r => simp only [bindOldA] at hb; contradiction
          · rw [paddedAlice_invalid G R S.measurements ox a (by omega),CoarseCells.left_zero,zero_mul,zero_apply]
  | inr q =>
      cases hyb : decodeB G R y with
      | inl oy =>
          simp only [hxa,hyb]
          simp only [accepts,hxa,hyb] at hz
          by_cases hb : b.val<G.scenario.answersB+1
          · cases hv : valid R q a.val
            · rw [newPartition_invalid G R E hE q a hv,CoarseCells.left_zero,zero_mul,zero_apply]
            · rw [paddedBob_valid G R S.measurements oy b hb]
              have ha : bindOldB R q oy a.val b.val=false := by simpa only [hb,decide_true,hv,Bool.true_and] using hz
              cases q with
              | oldAxis i g l => exact oldAxis_B_zero G R S hN E hE hEA he i g l oy ⟨b.val,hb⟩ a (of_decide_eq_true hv) ha k hk
              | slot r j => exact slot_B_zero G R S hN E hE hEA he r j (slot_question_bound R r j (decodeA_mem G R x _ hxa)) oy ⟨b.val,hb⟩ a (of_decide_eq_true hv) ha k hk
              | anchor => simp only [bindOldB] at ha; contradiction
              | cell g xx yy => simp only [bindOldB] at ha; contradiction
              | line g col l => simp only [bindOldB] at ha; contradiction
              | cross g h l m => simp only [bindOldB] at ha; contradiction
              | global isX => simp only [bindOldB] at ha; contradiction
              | pair j => simp only [bindOldB] at ha; contradiction
              | column r => simp only [bindOldB] at ha; contradiction
          · rw [paddedBob_invalid G R S.measurements oy b (by omega),CoarseCells.right_zero,mul_zero,zero_apply]
      | inr p =>
          simp only [hxa,hyb]
          simp only [accepts,hxa,hyb] at hz
          apply newRule_zero_of_directed G R E F hE hF (S.vector k) (fun i => hm i k hk)
          · exact directed_zero G R E F hE hF (S.vector k) (fun i => hm i k hk)
              (fun r => finite_slot_sum_zero G R S hR E he r k hk)
          · exact decodeA_mem G R x q hxa
          · exact decodeB_mem G R y p hyb
          · exact hz

/-- The concrete simultaneous honest family satisfies the entire frozen verifier. -/
theorem completeness (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hS : Perfect G S) (hR : RowsHold R S) (hN : NamedBinaryProjections R S) :
    ∃ T : NormalStrategy (scenario G R),Perfect (game G R) T ∧
      Extends (embedding G R) S T ∧ (FiniteMarginalEntropy S → FiniteMarginalEntropy T) := by
  obtain ⟨E,F,hE,hF,he,hf,hm⟩ := compressed_named G R S hR hN
  apply completeness_of_measurements G R S (honestMeasurements G R S.measurements E F hE hF)
  · exact honestMeasurements_oldA G R S.measurements E F hE hF
  · exact honestMeasurements_oldB G R S.measurements E F hE hF
  · exact honest_rejection_zero G R S hS hR hN E F hE hF he hf hm

end Sigma2.RowCompleteness
