import Sigma2.Purification
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.PureTransfer
open Coefficients TensorLifts

def flipScenario (s : Scenario) : Scenario :=
  ⟨s.questionsB,s.questionsA,s.answersB,s.answersA⟩

def flipMeasurements {s} (M : Measurements s) : Measurements (flipScenario s) :=
  TensorLifts.measurements _ M.bob M.alice M.bob_pos M.alice_pos M.bob_sum M.alice_sum

def flipNormal {s} (S : NormalStrategy s) : NormalStrategy (flipScenario s) where
  measurements := flipMeasurements S.measurements
  vector := fun k => swap (S.vector k)
  unit k := (swap.norm_map _).trans (S.unit k)
  weight := S.weight
  weight_nonneg := S.weight_nonneg
  weight_summable := S.weight_summable
  weight_sum := S.weight_sum

def flipPure {s} (T : PureStrategy s) : PureStrategy (flipScenario s) :=
  ⟨flipMeasurements T.measurements,swap T.vector,(swap.norm_map _).trans T.unit⟩

theorem swap_left (A : Op) (v : AB) : swap (left A v)=right A (swap v) := by
  ext ⟨i,j⟩
  rw [swap_apply,left_apply,right_apply]
  rfl

theorem swap_right (B : Op) (v : AB) : swap (right B v)=left B (swap v) := by
  ext ⟨i,j⟩
  rw [swap_apply,left_apply,right_apply]
  rfl

theorem swap_joint (A B : Op) (v : AB) :
    swap ((left A*right B) v)=(left B*right A) (swap v) := by
  change swap (left A (right B v))=left B (right A (swap v))
  rw [swap_left,swap_right]
  exact congrArg (fun L : BipOp => L (swap v)) (commute B A).symm

theorem flip_event {s} (M : Measurements s) (v : AB) (x : QA s) (y : QB s) (a : AA s) (b : BB s) :
    inner ℂ (swap v) (((flipMeasurements M).left y b*(flipMeasurements M).right x a) (swap v))=
      inner ℂ v ((M.left x a*M.right y b) v) := by
  rw [measurements_left,measurements_right]
  change inner ℂ (swap v) ((left (M.bob y b)*right (M.alice x a)) (swap v))=_
  rw [← swap_joint,swap.inner_map_map]

theorem flipNormal_probability {s} (S : NormalStrategy s) (x : QA s) (y : QB s) (a : AA s) (b : BB s) :
    (flipNormal S).probability y x b a=S.probability x y a b := by
  apply tsum_congr
  intro k
  change S.weight k*(inner ℂ (swap (S.vector k))
    (((flipMeasurements S.measurements).left y b*
      (flipMeasurements S.measurements).right x a) (swap (S.vector k)))).re=_
  rw [flip_event]
  rfl

theorem flipPure_probability {s} (T : PureStrategy s) (x : QA s) (y : QB s) (a : AA s) (b : BB s) :
    (flipPure T).probability y x b a=T.probability x y a b := by
  exact congrArg Complex.re (flip_event T.measurements T.vector x y a b)

/-- Purify on Bob's side to preserve Alice's actual operators and actual marginal. -/
theorem preserving_alice {s} (S : NormalStrategy s) :
    ∃ T : PureStrategy s,
      T.measurements.alice=S.measurements.alice ∧
      T.measurements.bob=(fun y b => Purification.amplify (S.measurements.bob y b)) ∧
      (∀ h : Density,MarginalA S h → MarginalA (normalOfPure T) h) ∧
      (∀ x y a b,S.probability x y a b=T.probability x y a b) := by
  obtain ⟨U,hU,hm,hp⟩ := Purification.exists_pure_preserving_bob (flipNormal S)
  let T : PureStrategy s := flipPure U
  refine ⟨T,?_,?_,?_,?_⟩
  · change U.measurements.bob=S.measurements.alice
    rw [hU]
    rfl
  · change U.measurements.alice=(fun y b => Purification.amplify (S.measurements.bob y b))
    rw [hU]
    rfl
  · intro h hh
    change MarginalB (normalOfPure U) h
    apply hm h
    exact hh
  · intro x y a b
    calc
      S.probability x y a b=(flipNormal S).probability y x b a :=
        (flipNormal_probability S x y a b).symm
      _ = U.probability y x b a := hp y x b a
      _ = T.probability x y a b := (flipPure_probability U y x b a).symm

/-- Transfer any Alice-side conclusion from pure states with the original local
operators, marginal, and event table. No density inverse or changed target is used. -/
theorem transfer_alice {s} (S : NormalStrategy s) (h : Density) (hm : MarginalA S h)
    (P : (QA s → AA s → Op) → Density → Prop)
    (H : ∀ T : PureStrategy s,T.measurements.alice=S.measurements.alice →
      MarginalA (normalOfPure T) h →
      (∀ x y a b,S.probability x y a b=T.probability x y a b) →
      P T.measurements.alice h) : P S.measurements.alice h := by
  obtain ⟨T,hA,_,hM,hp⟩ := preserving_alice S
  simpa only [hA] using H T hA (hM h hm) hp

#print axioms preserving_alice
#print axioms transfer_alice
end Sigma2.PureTransfer
