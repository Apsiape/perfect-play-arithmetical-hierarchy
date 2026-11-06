import Sigma2.RowCompletenessFamily

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler RowGame TensorLifts FiniteAncilla Preliminaries

/-- The explicit old/old synchronization conjunct is already a zero event of S. -/
theorem oldSync_zero {s} (R : Rows s) (S : NormalStrategy s)
    (hs : ∀ i,BinaryEventSynchronized S (R.event i)) (x y a b)
    (hz : oldSync R x y a.val b.val=false) : S.probability x y a b=0 := by
  by_contra hprob
  have he : oldSync R x y a.val b.val=true := by
    simp only [oldSync,List.all_eq_true]
    intro i hi
    split_ifs with hxy
    · rw [decide_eq_true_eq]
      by_contra hab
      apply hprob
      obtain ⟨rfl,rfl⟩ := hxy
      apply hs i
      simpa only [Fin.ext_iff] using hab
    · rfl
  rw [hz] at he
  contradiction

/-- Every originally sampled losing event of a perfect strategy is zero. -/
theorem perfect_event_zero (G : Game) (S : NormalStrategy G.scenario) (hS : Perfect G S)
    (x y a b) (hd : G.distribution x y≠0) (ha : G.accepts x y a b=false) :
    S.probability x y a b=0 := by
  change loss G S=0 at hS
  have hh := losing_event_le_loss G S x y a b
  simp only [ha,Bool.false_eq_true,ite_false,hS] at hh
  have hp : (0:ℝ)<(G.distribution x y:ℝ) := by
    exact_mod_cast lt_of_le_of_ne (G.distribution_nonneg x y) (Ne.symm hd)
  apply le_antisymm _ (probability_nonnegative S x y a b)
  by_contra hprob
  exact (not_lt_of_ge hh) (mul_pos hp (lt_of_not_ge hprob))

theorem old_rule_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hS : Perfect G S) (hN : NamedBinaryProjections R S) (x y a b)
    (hz : ((if G.distribution x y=0 then true else G.accepts x y a b) &&
      oldSync R x y a.val b.val)=false) : S.probability x y a b=0 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hs⟩ := hN
  by_cases hsync : oldSync R x y a.val b.val=false
  · exact oldSync_zero R S hs x y a b hsync
  · have ht : oldSync R x y a.val b.val=true := by cases hv : oldSync R x y a.val b.val <;> simp_all
    by_cases hd : G.distribution x y=0
    · simp [hd,ht] at hz
    · have ha : G.accepts x y a b=false := by simpa [hd,ht] using hz
      exact perfect_event_zero G S hS x y a b hd ha

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

/-- Old padding outcomes are literal zero operators, not merely zero marginals. -/
theorem paddedAlice_invalid (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (x : QA G.scenario) (a : AA (scenario G R)) (ha : G.scenario.answersA+1 ≤ a.val) :
    (paddedAlice G R M x).effect a=0 := by
  apply POVM.coarse_outside
  intro b he
  have hh := congrArg Fin.val he
  have hb := b.isLt
  dsimp only [embedding] at hh
  omega

theorem paddedBob_invalid (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (y : QB G.scenario) (b : BB (scenario G R)) (hb : G.scenario.answersB+1 ≤ b.val) :
    (paddedBob G R M y).effect b=0 := by
  apply POVM.coarse_outside
  intro a he
  have hh := congrArg Fin.val he
  have ha := a.isLt
  dsimp only [embedding] at hh
  omega

/-- All retained old/old rejections vanish on every original positive-weight component. -/
theorem honest_old_old_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hS : Perfect G S) (hN : NamedBinaryProjections R S)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i))
    (x y a b) (hz : (game G R).accepts ((embedding G R).qA x) ((embedding G R).qB y)
      ((embedding G R).aA a) ((embedding G R).aB b)=false)
    (k : ℕ) (hk : 0<S.weight k) :
    ((honestMeasurements G R S.measurements E F hE hF).left ((embedding G R).qA x) ((embedding G R).aA a)*
      (honestMeasurements G R S.measurements E F hE hF).right ((embedding G R).qB y) ((embedding G R).aB b))
        (entangle (RowSlots.dimension R) (S.vector k))=0 := by
  have hprob : S.probability x y a b=0 := by
    apply old_rule_zero G R S hS hN x y a b
    change accepts G R _ _ _ _=false at hz
    rw [accepts,decodeA_old,decodeB_old] at hz
    simpa only [embedding,dif_pos a.isLt,dif_pos b.isLt] using hz
  have hj := component_event_zero S x y a b hprob k hk
  rw [measurements_left,measurements_right] at hj
  rw [measurements_left,measurements_right,honestMeasurements_oldA,honestMeasurements_oldB]
  change left (amplify _ _) (right (amplify _ _) (entangle _ (S.vector k)))=0
  rw [right_entangle,left_entangle]
  change entangle (RowSlots.dimension R) ((left _*right _) (S.vector k))=0
  rw [hj,map_zero]

end Sigma2.RowCompleteness
