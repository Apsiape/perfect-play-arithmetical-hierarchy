import Sigma2.RowCompletenessOldBindings
import Sigma2.RowCompletenessDirected

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns FiniteAncilla TensorLifts

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem amplified_event_zero (d : ℕ) [NeZero d] (A B : Op) (v : AB)
    (hz : (left A*right B) v=0) :
    (left (amplify d A)*right (amplify d B)) (entangle d v)=0 := by
  change left _ (right _ _)=0
  rw [right_entangle,left_entangle]
  change entangle d ((left A*right B) v)=0
  rw [hz,map_zero]

theorem binary_axis_commute {s} (R : Rows s) (A : Op) (u : Bool)
    (g : Fin (RowSlots.squares R)) (k : Fin 4) (neg : Bool) :
    Commute (binaryEffect (amplify (RowSlots.dimension R) A) u) (spectralEffect (rowAxis R g k) neg) := by
  apply commute_spectral
  cases u
  · exact (Commute.one_left _).sub_left (rowAxis_amplify R g k A)
  · exact rowAxis_amplify R g k A

theorem slot_realized_formula (n j : ℕ) (hj : j<2^n) (E : Op) (hE : Projection E) (u : Bool) (c : Fin 3) :
    (realizePartition (slotPartition n j hj E hE)).effect (u,c)=amplify (2^n) (binaryEffect E u)*
      matrixOp (2^n) (((pairPartition n j hj).coarse pairClass).effect c) := by
  change matrixOp _ _=_
  rw [slot_binary_formula,matrixOp_mul,matrixOp_constantDiagonal]

theorem oldAxis_div (u neg : Bool) : (2*bit u+bitAnswer neg)/2=bit u := by
  cases u <;> cases neg <;> rfl

theorem bit_eq_one (u : Bool) : bit u=1 ↔ u=true := by cases u <;> decide

theorem oldAxis_A_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hN : NamedBinaryProjections R S) (F : Fin R.count → Op) (hF : ∀ i,Projection (F i))
    (hf : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (hfB : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k))
    (i : Fin R.count) (g : Fin (RowSlots.squares R)) (l : Fin 4) (x : QA G.scenario) (a : AA G.scenario)
    (b : AA (scenario G R)) (hb : b.val<4) (hz : bindOldA R x (.oldAxis i g l) a.val b.val=false)
    (k : ℕ) (hk : 0<S.weight k) :
    (left (amplify (RowSlots.dimension R) (S.measurements.alice x a))*
      right ((newPartition G R F hF (.oldAxis i g l)).effect b)) (entangle (RowSlots.dimension R) (S.vector k))=0 := by
  by_cases hx : x=(R.event i).x
  · subst x
    obtain ⟨u,neg,hb⟩ := decode_oldAxis_answer b.val hb
    rw [oldAxis_effect G R F hF i g l (u,neg) b hb]
    apply scalar_factor_A_zero _ _ _ _ (binary_axis_commute R (F i) u g l neg)
    rw [binary_amplify]
    apply amplified_event_zero
    have hne : ¬(a=(R.event i).a ↔ u=true) := by
      simpa only [bindOldA,ite_true,hb,oldAxis_div,bit_eq_one,decide_eq_false_iff_not,Fin.ext_iff] using hz
    simpa only [measurements_left] using old_binary_A_zero G R S hN F hF hf hfB i a u hne k hk
  · simp only [bindOldA,if_neg hx] at hz
    contradiction

theorem oldAxis_B_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hN : NamedBinaryProjections R S) (E : Fin R.count → Op) (hE : ∀ i,Projection (E i))
    (he : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k))
    (heA : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (i : Fin R.count) (g : Fin (RowSlots.squares R)) (l : Fin 4) (y : QB G.scenario) (b : BB G.scenario)
    (a : AA (scenario G R)) (ha : a.val<4) (hz : bindOldB R (.oldAxis i g l) y a.val b.val=false)
    (k : ℕ) (hk : 0<S.weight k) :
    (left ((newPartition G R E hE (.oldAxis i g l)).effect a)*
      right (amplify (RowSlots.dimension R) (S.measurements.bob y b))) (entangle (RowSlots.dimension R) (S.vector k))=0 := by
  by_cases hy : y=(R.event i).y
  · subst y
    obtain ⟨u,neg,ha⟩ := decode_oldAxis_answer a.val ha
    rw [oldAxis_effect G R E hE i g l (u,neg) a ha]
    apply scalar_factor_B_zero _ _ _ _ (binary_axis_commute R (E i) u g l neg)
    rw [binary_amplify]
    apply amplified_event_zero
    have hne : ¬(b=(R.event i).b ↔ u=true) := by
      simpa only [bindOldB,ite_true,ha,oldAxis_div,bit_eq_one,decide_eq_false_iff_not,Fin.ext_iff] using hz
    simpa only [measurements_right] using old_binary_B_zero G R S hN E hE he heA i b u hne k hk
  · simp only [bindOldB,if_neg hy] at hz
    contradiction

theorem slot_A_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hN : NamedBinaryProjections R S) (F : Fin R.count → Op) (hF : ∀ i,Projection (F i))
    (hf : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (hfB : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k))
    (r : Fin R.rowCount) (j : ℕ) (hj : j<2^(bits R)) (x : QA G.scenario) (a : AA G.scenario)
    (b : AA (scenario G R)) (hb : b.val<6) (hz : bindOldA R x (.slot r j) a.val b.val=false)
    (k : ℕ) (hk : 0<S.weight k) :
    (left (amplify (RowSlots.dimension R) (S.measurements.alice x a))*
      right ((newPartition G R F hF (.slot r j)).effect b)) (entangle (RowSlots.dimension R) (S.vector k))=0 := by
  cases hev : (RowSlots.slot R r j).event with
  | none =>
      have hne : b.val/3≠1 := by simpa only [bindOldA,hev,decide_eq_false_iff_not] using hz
      rw [slot_anchor_binding_zero G R F hF r j hj hev b hb hne,CoarseCells.right_zero,mul_zero,zero_apply]
  | some i =>
      by_cases hx : x=(R.event i).x
      · subst x
        obtain ⟨u,c,hb⟩ := decode_slot_answer b.val hb
        have hdiv : b.val/3=bit u := by have := c.isLt; omega
        rw [slot_effect G R F hF r j hj (u,c) b hb,slot_realized_formula]
        have hs : slotEvent R F r j=F i := by simp only [slotEvent,hev]
        simp only [hs,RowScalar.dimension_bits]
        apply scalar_factor_A_zero
        · exact scalarBlocks_amplify _ _ (scalar_coarse (pairPartition (bits R) j hj)
            (scalar_pair (bits R) j hj) pairClass c) _
        · apply amplified_event_zero
          have hne : ¬(a=(R.event i).a ↔ u=true) := by
            simpa only [bindOldA,hev,ite_true,hdiv,bit_eq_one,decide_eq_false_iff_not,Fin.ext_iff] using hz
          simpa only [measurements_left] using old_binary_A_zero G R S hN F hF hf hfB i a u hne k hk
      · simp only [bindOldA,hev,if_neg hx] at hz
        contradiction

theorem slot_B_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hN : NamedBinaryProjections R S) (E : Fin R.count → Op) (hE : ∀ i,Projection (E i))
    (he : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k))
    (heA : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (r : Fin R.rowCount) (j : ℕ) (hj : j<2^(bits R)) (y : QB G.scenario) (b : BB G.scenario)
    (a : AA (scenario G R)) (ha : a.val<6) (hz : bindOldB R (.slot r j) y a.val b.val=false)
    (k : ℕ) (hk : 0<S.weight k) :
    (left ((newPartition G R E hE (.slot r j)).effect a)*
      right (amplify (RowSlots.dimension R) (S.measurements.bob y b))) (entangle (RowSlots.dimension R) (S.vector k))=0 := by
  cases hev : (RowSlots.slot R r j).event with
  | none =>
      have hne : a.val/3≠1 := by simpa only [bindOldB,hev,decide_eq_false_iff_not] using hz
      rw [slot_anchor_binding_zero G R E hE r j hj hev a ha hne,CoarseCells.left_zero,zero_mul,zero_apply]
  | some i =>
      by_cases hy : y=(R.event i).y
      · subst y
        obtain ⟨u,c,ha⟩ := decode_slot_answer a.val ha
        have hdiv : a.val/3=bit u := by have := c.isLt; omega
        rw [slot_effect G R E hE r j hj (u,c) a ha,slot_realized_formula]
        have hs : slotEvent R E r j=E i := by simp only [slotEvent,hev]
        simp only [hs,RowScalar.dimension_bits]
        apply scalar_factor_B_zero
        · exact scalarBlocks_amplify _ _ (scalar_coarse (pairPartition (bits R) j hj)
            (scalar_pair (bits R) j hj) pairClass c) _
        · apply amplified_event_zero
          have hne : ¬(b=(R.event i).b ↔ u=true) := by
            simpa only [bindOldB,hev,ite_true,hdiv,bit_eq_one,decide_eq_false_iff_not,Fin.ext_iff] using hz
          simpa only [measurements_right] using old_binary_B_zero G R S hN E hE he heA i b u hne k hk
      · simp only [bindOldB,hev,if_neg hy] at hz
        contradiction

end Sigma2.RowCompleteness
