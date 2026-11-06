import Sigma2.RowGame
import Sigma2.RowSynchronization

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowRestriction
open Compiler RowGame CoarseCells TensorLifts Preliminaries

/-- Unused padded outcomes are folded into answer zero. The perfect-game proof
below shows their correlations vanish, so this gives an actual old strategy. -/
def foldA (G : Game) (R : Rows G.scenario) (a : AA (scenario G R)) : AA G.scenario :=
  if h : a.val<G.scenario.answersA+1 then ⟨a.val,h⟩ else 0

def foldB (G : Game) (R : Rows G.scenario) (b : BB (scenario G R)) : BB G.scenario :=
  if h : b.val<G.scenario.answersB+1 then ⟨b.val,h⟩ else 0

def measurements (G : Game) (R : Rows G.scenario) (T : NormalStrategy (scenario G R)) :
    Measurements G.scenario :=
  TensorLifts.measurements G.scenario
    (fun x a => coarse (T.measurements.alice ((embedding G R).qA x)) (foldA G R) a)
    (fun y b => coarse (T.measurements.bob ((embedding G R).qB y)) (foldB G R) b)
    (fun _x _a => coarse_positive _ _ _ (T.measurements.alice_pos _))
    (fun _y _b => coarse_positive _ _ _ (T.measurements.bob_pos _))
    (fun _x => (coarse_sum _ _).trans (T.measurements.alice_sum _))
    (fun _y => (coarse_sum _ _).trans (T.measurements.bob_sum _))

def restrict (G : Game) (R : Rows G.scenario) (T : NormalStrategy (scenario G R)) :
    NormalStrategy G.scenario where
  measurements := measurements G R T
  vector := T.vector
  unit := T.unit
  weight := T.weight
  weight_nonneg := T.weight_nonneg
  weight_summable := T.weight_summable
  weight_sum := T.weight_sum

theorem left_coarse {ι τ : Type} [Fintype ι] [DecidableEq τ]
    (A : ι → Op) (p : ι → τ) (t : τ) :
    left (coarse A p t)=∑ a, if p a=t then left (A a) else 0 := by
  rw [coarse, left_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem right_coarse {ι τ : Type} [Fintype ι] [DecidableEq τ]
    (A : ι → Op) (p : ι → τ) (t : τ) :
    right (coarse A p t)=∑ a, if p a=t then right (A a) else 0 := by
  rw [coarse, right_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

theorem component_probability (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (k x y a b) :
    ((restrict G R T).component k).probability x y a b =
      ∑ aa, ∑ bb, if foldA G R aa=a then if foldB G R bb=b then
        (T.component k).probability ((embedding G R).qA x) ((embedding G R).qB y) aa bb
      else 0 else 0 := by
  simp only [PureStrategy.probability, measurements_left, measurements_right]
  change (inner ℂ (T.vector k) ((left (coarse _ _ a)*right (coarse _ _ b)) (T.vector k))).re = _
  rw [left_coarse, right_coarse]
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, sum_apply, inner_sum, complex_re_sum]
  apply Finset.sum_congr rfl
  intro aa _
  apply Finset.sum_congr rfl
  intro bb _
  split_ifs <;> simp_all [NormalStrategy.component]

theorem probability (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (x y a b) :
    (restrict G R T).probability x y a b =
      ∑ aa, ∑ bb, if foldA G R aa=a then if foldB G R bb=b then
        T.probability ((embedding G R).qA x) ((embedding G R).qB y) aa bb
      else 0 else 0 := by
  let f := fun aa bb k => T.weight k * (if foldA G R aa=a then if foldB G R bb=b then
      (T.component k).probability ((embedding G R).qA x) ((embedding G R).qB y) aa bb else 0 else 0)
  have hf aa bb : Summable (f aa bb) := by
    dsimp [f]
    split_ifs
    · exact event_summable T _ _ aa bb
    all_goals simp only [mul_zero]; exact summable_zero
  have hh : (restrict G R T).probability x y a b=∑' k, ∑ aa, ∑ bb, f aa bb k := by
    unfold NormalStrategy.probability
    change (∑' k, T.weight k * ((restrict G R T).component k).probability x y a b)=_
    simp only [component_probability, Finset.mul_sum]
    rfl
  rw [hh, Summable.tsum_finsetSum (fun aa _ => summable_sum (fun bb _ => hf aa bb))]
  apply Finset.sum_congr rfl
  intro aa _
  rw [Summable.tsum_finsetSum (fun bb _ => hf aa bb)]
  apply Finset.sum_congr rfl
  intro bb _
  dsimp [f]
  split_ifs <;> simp [NormalStrategy.probability]

/-- Padding on an old/old pair is always rejected. -/
theorem padded_probability (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (hT : Perfect (game G R) T) (x y aa bb)
    (h : G.scenario.answersA+1 ≤ aa.val ∨ G.scenario.answersB+1 ≤ bb.val) :
    T.probability ((embedding G R).qA x) ((embedding G R).qB y) aa bb=0 := by
  apply rejected_probability G R T hT
  change accepts G R _ _ _ _=false
  simp only [accepts, decodeA_old, decodeB_old]
  rcases h with h | h
  · simp [show ¬ aa.val<G.scenario.answersA+1 by omega]
  · simp [show ¬ bb.val<G.scenario.answersB+1 by omega]

theorem restriction_extends (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (hT : Perfect (game G R) T) :
    Extends (embedding G R) (restrict G R T) T := by
  intro x y a b
  rw [probability]
  have hterm (aa : AA (scenario G R)) (bb : BB (scenario G R)) :
      (if foldA G R aa=a then if foldB G R bb=b then
        T.probability ((embedding G R).qA x) ((embedding G R).qB y) aa bb else 0 else 0) =
      (if aa=(embedding G R).aA a then if bb=(embedding G R).aB b then
        T.probability ((embedding G R).qA x) ((embedding G R).qB y) aa bb else 0 else 0) := by
    by_cases ha : aa.val<G.scenario.answersA+1
    · by_cases hb : bb.val<G.scenario.answersB+1
      · have ea : foldA G R aa=a ↔ aa=(embedding G R).aA a := by
          simp only [foldA, ha, dite_true, embedding, Fin.ext_iff]
        have eb : foldB G R bb=b ↔ bb=(embedding G R).aB b := by
          simp only [foldB, hb, dite_true, embedding, Fin.ext_iff]
        simp only [ea,eb]
      · have hz := padded_probability G R T hT x y aa bb (Or.inr (by omega))
        simp [hz]
    · have hz := padded_probability G R T hT x y aa bb (Or.inl (by omega))
      simp [hz]
  simp_rw [hterm]
  simp

theorem perfect (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (hT : Perfect (game G R) T) :
    Perfect G (restrict G R T) := by
  unfold Perfect loss
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  by_cases hd : G.distribution x y=0
  · simp [hd]
  · cases hl : G.accepts x y a b
    · simp only [hl, Bool.false_eq_true, ite_false]
      rw [restriction_extends G R T hT x y a b]
      rw [rejected_probability G R T hT _ _ _ _ (retains_losing G R x y a b hd hl), mul_zero]
    · simp [hl]

/-- Restriction keeps the original ensemble exactly, hence both actual
marginals and their spectral entropy predicates are definitionally unchanged. -/
theorem entropy_restrict (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) :
    FiniteMarginalEntropy (restrict G R T) ↔ FiniteMarginalEntropy T := Iff.rfl
/-- The concrete old/old matching rule supplies every named binary event
on the restricted strategy, without assuming the row conclusion. -/
theorem synchronized (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (hT : Perfect (game G R) T)
    (i : Fin R.count) : BinaryEventSynchronized (restrict G R T) (R.event i) := by
  intro a b hab
  rw [restriction_extends G R T hT]
  apply rejected_probability G R T hT
  have hs : oldSync R (R.event i).x (R.event i).y a.val b.val=false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh := (List.all_eq_true.mp h) i (List.mem_finRange i)
    apply hab
    simpa [Fin.ext_iff] using hh
  change accepts G R _ _ _ _=false
  simp only [accepts, decodeA_old, decodeB_old]
  simp [embedding, a.isLt, b.isLt, hs]

/-- Actual supplier call at the newly constructed row-game restriction.
The four-bridge pre-row assembly is a different call site and remains open. -/
theorem named (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (hT : Perfect (game G R) T) :
    NamedBinaryProjections R (restrict G R T) :=
  RowSynchronization.named_of_synchronized R (restrict G R T) (synchronized G R T hT)

#print axioms restrict
#print axioms restriction_extends
#print axioms perfect
#print axioms named
end Sigma2.RowRestriction



