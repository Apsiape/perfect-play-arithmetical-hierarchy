import Sigma2.RowCompletenessContextBindings

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns FiniteAncilla

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem axis_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (g : Fin (RowSlots.squares R)) (k : Fin 4)
    (b : Bool) (a : AA (scenario G R)) (ha : a.val=bitAnswer b) :
    (newPartition G R E hE (axis R g k)).effect a=spectralEffect (rowAxis R g k) b := by
  fin_cases k
  · exact cell_effect G R E hE g 0 0 b a ha
  · exact cell_effect G R E hE g 1 0 b a ha
  · exact cell_effect G R E hE g 1 1 b a ha
  · exact cell_effect G R E hE g 0 1 b a ha

theorem line_binding_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (g : Fin (RowSlots.squares R)) (col : Bool) (k j : Fin 3)
    (a b : AA (scenario G R)) (ha : a.val<4) (hb : b.val<2)
    (hne : b.val≠bitAnswer (cellSign (col && decide (k.val=2)) a.val j.val)) :
    (newPartition G R E hE (.line g col k)).effect a*
      (newPartition G R E hE (if col then .cell g j k else .cell g k j)).effect b=0 := by
  obtain ⟨u,w,ha⟩ := decode_line_answer a.val ha
  obtain ⟨t,hb⟩ := decode_cell_answer b.val hb
  rw [line_effect G R E hE g col k (u,w) a ha]
  have he : (newPartition G R E hE (if col then .cell g j k else .cell g k j)).effect b=
      spectralEffect (rowContext R g col k j) t := by
    cases col <;> exact cell_effect G R E hE _ _ _ t b hb
  rw [he]
  have hr := rowMagic_relations R g
  have hs : star (rowContext R g col k j)=rowContext R g col k j := by
    cases col
    · exact hr.selfadjoint k j
    · exact hr.selfadjoint j k
  have hq : rowContext R g col k j*rowContext R g col k j=1 := by
    cases col
    · exact hr.square k j
    · exact hr.square j k
  have ht : cellSign (col && decide (k.val=2)) (2*bit u+bit w) j.val≠t := by
    intro h
    apply hne
    rw [hb,ha,h]
  exact (spectral_action _ _ hs hq _ t (rowContext_eigen R g col k u w j)).trans (if_neg ht)

theorem decode_cross_answer (v : ℕ) (hv : v<4) : ∃ b c : Bool,v=2*bitAnswer b+bitAnswer c := by
  interval_cases v
  · exact ⟨true,true,rfl⟩
  · exact ⟨true,false,rfl⟩
  · exact ⟨false,true,rfl⟩
  · exact ⟨false,false,rfl⟩

theorem decode_oldAxis_answer (v : ℕ) (hv : v<4) : ∃ b c : Bool,v=2*bit b+bitAnswer c := by
  interval_cases v
  · exact ⟨false,true,rfl⟩
  · exact ⟨false,false,rfl⟩
  · exact ⟨true,true,rfl⟩
  · exact ⟨true,false,rfl⟩

theorem encoded_div (b c : Bool) : (2*bitAnswer b+bitAnswer c)/2=bitAnswer b := by
  cases b <;> cases c <;> rfl

theorem encoded_mod (b c : Bool) : (2*bitAnswer b+bitAnswer c)%2=bitAnswer c := by
  cases b <;> cases c <;> rfl

theorem cross_binding_first_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (g h : Fin (RowSlots.squares R)) (hgh : g≠h) (k l : Fin 4)
    (a b : AA (scenario G R)) (ha : a.val<4) (hb : b.val<2) (hne : b.val≠a.val/2) :
    (newPartition G R E hE (.cross g h k l)).effect a*
      (newPartition G R E hE (axis R g k)).effect b=0 := by
  obtain ⟨u,w,ha⟩ := decode_cross_answer a.val ha
  obtain ⟨t,hb⟩ := decode_cell_answer b.val hb
  rw [cross_effect G R E hE g h hgh k l (u,w) a ha,axis_effect G R E hE g k t b hb]
  have ht : u≠t := by intro he; apply hne; rw [hb,ha,encoded_div,he]
  rw [spectral_action _ _ (rowAxis_star R g k) (rowAxis_square R g k) u t
    (joint_eigen_first _ _ (rowAxis_star R g k) (rowAxis_square R g k) (crossAxis_commute R g h hgh k l) u w),if_neg ht]

theorem cross_binding_second_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (g h : Fin (RowSlots.squares R)) (hgh : g≠h) (k l : Fin 4)
    (a b : AA (scenario G R)) (ha : a.val<4) (hb : b.val<2) (hne : b.val≠a.val%2) :
    (newPartition G R E hE (.cross g h k l)).effect a*
      (newPartition G R E hE (axis R h l)).effect b=0 := by
  obtain ⟨u,w,ha⟩ := decode_cross_answer a.val ha
  obtain ⟨t,hb⟩ := decode_cell_answer b.val hb
  rw [cross_effect G R E hE g h hgh k l (u,w) a ha,axis_effect G R E hE h l t b hb]
  have ht : w≠t := by intro he; apply hne; rw [hb,ha,encoded_mod,he]
  rw [spectral_action _ _ (rowAxis_star R h l) (rowAxis_square R h l) w t
    (joint_eigen_second _ _ (rowAxis_star R h l) (rowAxis_square R h l) u w),if_neg ht]

theorem oldAxis_binding_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (i : Fin R.count) (g : Fin (RowSlots.squares R)) (k : Fin 4)
    (a b : AA (scenario G R)) (ha : a.val<4) (hb : b.val<2) (hne : b.val≠a.val%2) :
    (newPartition G R E hE (.oldAxis i g k)).effect a*
      (newPartition G R E hE (axis R g k)).effect b=0 := by
  obtain ⟨u,w,ha⟩ := decode_oldAxis_answer a.val ha
  obtain ⟨t,hb⟩ := decode_cell_answer b.val hb
  rw [oldAxis_effect G R E hE i g k (u,w) a ha,axis_effect G R E hE g k t b hb]
  have ht : w≠t := by
    intro he
    apply hne
    rw [hb,ha]
    cases u <;> cases w <;> simpa only [bit,bitAnswer,Bool.false_eq_true,Bool.true_eq,ite_true,ite_false] using congrArg bitAnswer he.symm
  rw [mul_assoc,spectral_action _ _ (rowAxis_star R g k) (rowAxis_square R g k) w t
    (spectral_eigen _ (rowAxis_star R g k) (rowAxis_square R g k) w),if_neg ht,mul_zero]

end Sigma2.RowCompleteness
