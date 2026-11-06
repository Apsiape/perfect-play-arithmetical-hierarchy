import Sigma2.CompilerApproxDirected

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000
noncomputable section
namespace Sigma2.CompilerApproxRejection
open Compiler CompilerScaffold CompilerEventLoss RowCompleteness RowGame RowColumns
  FiniteAncilla TensorLifts CompilerApproxRows CompilerApproxDirected

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

/-- Excludes exactly the two row-zero orientations of discarded rows. -/
def OutsideRows (G : Game) (R : Rows G.scenario) (keep : Fin R.rowCount → Prop)
    (x : QA (scenario G R)) (y : QB (scenario G R)) (a : AA (scenario G R))
    (b : BB (scenario G R)) : Prop :=
  ∀ q p, decodeA G R x=.inr q → decodeB G R y=.inr p →
    ¬ (RowException R keep q p a.val b.val ∨ RowException R keep p q b.val a.val)

theorem honest_rejection_zero_on (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hS : Perfect G S) (keep : Fin R.rowCount → Prop) (hR : RowsHoldOn R S keep) (hN : NamedBinaryProjections R S)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i))
    (he : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (hf : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k))
    (hm : ∀ i k,0<S.weight k → left (E i) (S.vector k)=right (F i) (S.vector k))
    (x : QA (scenario G R)) (y : QB (scenario G R))
    (a : AA (scenario G R)) (b : BB (scenario G R)) (hgood : OutsideRows G R keep x y a b) (hz : (game G R).accepts x y a b=false) (k : ℕ) (hk : 0<S.weight k) :
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
          apply newRule_zero_on G R E F hE hF (S.vector k) (fun i => hm i k hk) keep
          · exact directed_zero_on G R E F hE hF (S.vector k) (fun i => hm i k hk) keep
              (fun r hr => finite_slot_sum_zero_on G R S keep hR E he r hr k hk)
          · exact decodeA_mem G R x q hxa
          · exact decodeB_mem G R y p hyb
          · exact hgood q p hxa hyb
          · exact hz

/-- Every structural or old/old event is outside the application row-zero tests. -/
theorem class_outside (P : Presentation) (x y a b) (c : TestClass)
    (hc : c=.structural ∨ c=.preGame) (he : testClass P x y a b=c) :
    OutsideRows (preGame P) (rows P) (fun r => ¬ applicationRow P r) x y a b := by
  classical
  intro q p hx hy hbad
  rcases hbad with ⟨r,hr,hq,hp,ha,hb⟩ | ⟨r,hr,hp,hq,hb,ha⟩
  · subst q; subst p
    have happ : applicationRow P r := Classical.not_not.mp hr
    have ha' : a=0 := Fin.ext ha
    have hb' : b=0 := Fin.ext hb
    have ht : testClass P x y a b=.applicationForward := by
      simp only [testClass,hx,hy,happ,ha',hb',and_self,ite_true]
    rw [ht] at he
    rcases hc with hc | hc <;> rw [hc] at he <;> contradiction
  · subst q; subst p
    have happ : applicationRow P r := Classical.not_not.mp hr
    have ha' : a=0 := Fin.ext ha
    have hb' : b=0 := Fin.ext hb
    have ht : testClass P x y a b=.applicationReverse := by
      simp only [testClass,hx,hy,happ,ha',hb',and_self,ite_true]
    rw [ht] at he
    rcases hc with hc | hc <;> rw [hc] at he <;> contradiction

/-- The frozen honest family has zero structural and preGame contributions,
without any equation on application rows. -/
theorem honest_class_zero (P : Presentation) (S : NormalStrategy (preGame P).scenario)
    (hS : Perfect (preGame P) S) (hR : StructuralRowsHold P S)
    (hN : NamedBinaryProjections (rows P) S)
    (E F : Fin (rows P).count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i))
    (he : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.left ((rows P).event i).x ((rows P).event i).a (S.vector k))
    (hf : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.right ((rows P).event i).y ((rows P).event i).b (S.vector k))
    (hm : ∀ i k,0<S.weight k → left (E i) (S.vector k)=right (F i) (S.vector k))
    (c : TestClass) (hc : c=.structural ∨ c=.preGame) :
    classContribution P (withMeasurements (RowSlots.dimension (rows P)) S
      (honestMeasurements (preGame P) (rows P) S.measurements E F hE hF)) c=0 := by
  apply class_zero_of_annihilates
  intro x y a b hclass hz k hk
  change ((honestMeasurements (preGame P) (rows P) S.measurements E F hE hF).left x a*
    (honestMeasurements (preGame P) (rows P) S.measurements E F hE hF).right y b)
      (entangle (RowSlots.dimension (rows P)) (S.vector k))=0
  exact honest_rejection_zero_on (preGame P) (rows P) S hS
    (fun r => ¬ applicationRow P r) hR hN E F hE hF he hf hm x y a b
    (class_outside P x y a b c hc hclass) hz k
    (lt_of_le_of_ne (S.weight_nonneg k) (Ne.symm hk))

end Sigma2.CompilerApproxRejection
