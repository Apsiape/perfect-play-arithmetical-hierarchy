import Sigma2.RowCompletenessColumnBindings
import Sigma2.RowCompletenessOld

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns FiniteAncilla TensorLifts

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem complement_binding_zero (A F : Op) (hF : Projection F) (v : AB)
    (hm : left A v=right F v) : (left A*right (1-F)) v=0 := by
  have he : (left A*right F) v=left A v := by
    rw [commute]
    change right F (left A v)=left A v
    rw [hm]
    change (right F*right F) v=right F v
    rw [← right_mul,hF.2]
  rw [MagicRelations.right_sub,right_one,mul_sub,mul_one]
  change left A v-(left A*right F) v=0
  rw [he,sub_self]

theorem complement_binding_zero_B (E B : Op) (hE : Projection E) (v : AB)
    (hm : left E v=right B v) : (left (1-E)*right B) v=0 := by
  have he : (left E*right B) v=right B v := by
    change left E (right B v)=right B v
    rw [← hm]
    change (left E*left E) v=left E v
    rw [← left_mul,hE.2]
  rw [PureSupport.left_sub,left_one,sub_mul,one_mul]
  change right B v-(left E*right B) v=0
  rw [he,sub_self]

theorem old_binary_A_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hN : NamedBinaryProjections R S) (F : Fin R.count → Op) (hF : ∀ i,Projection (F i))
    (hf : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (hfB : ∀ i k,0<S.weight k → right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k))
    (i : Fin R.count) (a : AA G.scenario) (u : Bool)
    (hne : ¬(a=(R.event i).a ↔ u=true)) (k : ℕ) (hk : 0<S.weight k) :
    (S.measurements.left (R.event i).x a*right (binaryEffect (F i) u)) (S.vector k)=0 := by
  cases u
  · have ha : a=(R.event i).a := by simpa only [Bool.false_eq_true,iff_false,not_not] using hne
    subst a
    rw [measurements_left]
    exact complement_binding_zero _ _ (hF i) _ (by simpa only [measurements_left] using (hf i k hk).symm)
  · have ha : a≠(R.event i).a := by simpa only [iff_true] using hne
    obtain ⟨_,_,_,_,_,_,_,_,_,hsync⟩ := hN
    have hp : S.probability (R.event i).x (R.event i).y a (R.event i).b=0 := by
      apply hsync i
      simpa [ha]
    have he := component_event_zero S _ _ _ _ hp k hk
    change S.measurements.left _ a (right (F i) (S.vector k))=0
    rw [hfB i k hk]
    exact he

theorem old_binary_B_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hN : NamedBinaryProjections R S) (E : Fin R.count → Op) (hE : ∀ i,Projection (E i))
    (he : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k))
    (heA : ∀ i k,0<S.weight k → left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (i : Fin R.count) (b : BB G.scenario) (u : Bool)
    (hne : ¬(b=(R.event i).b ↔ u=true)) (k : ℕ) (hk : 0<S.weight k) :
    (left (binaryEffect (E i) u)*S.measurements.right (R.event i).y b) (S.vector k)=0 := by
  cases u
  · have hb : b=(R.event i).b := by simpa only [Bool.false_eq_true,iff_false,not_not] using hne
    subst b
    rw [measurements_right]
    exact complement_binding_zero_B _ _ (hE i) _ (by simpa only [measurements_right] using he i k hk)
  · have hb : b≠(R.event i).b := by simpa only [iff_true] using hne
    obtain ⟨_,_,_,_,_,_,_,_,_,hsync⟩ := hN
    have hp : S.probability (R.event i).x (R.event i).y (R.event i).a b=0 := by
      apply hsync i
      simpa [hb]
    have hz := component_event_zero S _ _ _ _ hp k hk
    rw [measurements_left,measurements_right] at hz
    rw [measurements_right]
    change (left (E i)*right (S.measurements.bob (R.event i).y b)) (S.vector k)=0
    rw [commute]
    change right _ (left (E i) (S.vector k))=0
    rw [heA i k hk,measurements_left]
    rw [commute] at hz
    exact hz

theorem amplify_sub (d : ℕ) [NeZero d] (A B : Op) : amplify d (A-B)=amplify d A-amplify d B := by
  calc
    amplify d (A-B)=amplify d (A+(-1:ℂ) • B) := by rw [show (-1:ℂ) • B= -B from neg_one_smul ℂ B,sub_eq_add_neg]
    _ = amplify d A+(-1:ℂ) • amplify d B := by rw [amplify_add,amplify_smul]
    _ = amplify d A-amplify d B := by rw [show (-1:ℂ) • amplify d B= -amplify d B from neg_one_smul ℂ (amplify d B),sub_eq_add_neg]

theorem binary_amplify (d : ℕ) [NeZero d] (A : Op) (b : Bool) :
    binaryEffect (amplify d A) b=amplify d (binaryEffect A b) := by
  cases b
  · change 1-amplify d A=amplify d (1-A)
    rw [amplify_sub,amplify_one]
  · rfl

theorem scalar_factor_A_zero (A B T : Op) (v : AB) (hc : Commute B T)
    (hz : (left A*right B) v=0) : (left A*right (B*T)) v=0 := by
  rw [hc.eq,right_mul,← mul_assoc,commute A T,mul_assoc]
  change right T ((left A*right B) v)=0
  rw [hz,map_zero]

theorem scalar_factor_B_zero (A B T : Op) (v : AB) (hc : Commute A T)
    (hz : (left A*right B) v=0) : (left (A*T)*right B) v=0 := by
  rw [hc.eq,left_mul,mul_assoc]
  change left T ((left A*right B) v)=0
  rw [hz,map_zero]

end Sigma2.RowCompleteness
