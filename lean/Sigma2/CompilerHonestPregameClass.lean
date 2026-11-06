import Sigma2.CompilerHonestFinalCorrect

/-! The padded final-game preGame class vanishes, including oldSync and
 invalid answers, for the corrected arbitrary-structural honest strategy. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
noncomputable section
namespace Sigma2.CompilerHonestPregameClass
open Compiler CompilerScaffold CompilerEventLoss RowGame RowCompleteness
  FiniteAncilla TensorLifts Preliminaries CompilerHonestFinalCorrect
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem old_old_zero (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (hS : Perfect G S) (hN : NamedBinaryProjections R S)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i))
    (x : QA (RowGame.scenario G R)) (y : QB (RowGame.scenario G R))
    (a : AA (RowGame.scenario G R)) (b : BB (RowGame.scenario G R))
    (ox : QA G.scenario) (oy : QB G.scenario)
    (hxa : decodeA G R x=.inl ox) (hyb : decodeB G R y=.inl oy)
    (hz : (game G R).accepts x y a b=false) (k : ℕ) (hk : 0<S.weight k) :
    ((honestMeasurements G R S.measurements E F hE hF).left x a*
      (honestMeasurements G R S.measurements E F hE hF).right y b)
        (entangle (RowSlots.dimension R) (S.vector k))=0 := by
  change accepts G R x y a b=false at hz
  rw [measurements_left,measurements_right,honest_A_effect,honest_B_effect,hxa,hyb]
  change (left ((paddedAlice G R S.measurements ox).effect a)*
    right ((paddedBob G R S.measurements oy).effect b))
      (entangle (RowSlots.dimension R) (S.vector k))=0
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

theorem preGame_decoded (P : Presentation) (x : QA (finalGame P).scenario)
    (y : QB (finalGame P).scenario) (a : AA (finalGame P).scenario) (b : BB (finalGame P).scenario)
    (hc : testClass P x y a b=.preGame) :
    ∃ ox oy,decodeA (preGame P) (rows P) x=.inl ox ∧ decodeB (preGame P) (rows P) y=.inl oy := by
  classical
  cases hx : decodeA (preGame P) (rows P) x with
  | inl ox =>
      cases hy : decodeB (preGame P) (rows P) y with
      | inl oy => exact ⟨ox,oy,rfl,rfl⟩
      | inr q => cases q <;> simp [testClass,hx,hy] at hc
  | inr q =>
      cases hy : decodeB (preGame P) (rows P) y with
      | inl oy => cases q <;> simp [testClass,hx,hy] at hc
      | inr p =>
          cases q <;> cases p <;> simp [testClass,hx,hy] at hc
          all_goals cases ‹Bool› <;> simp_all [testClass]
          all_goals split_ifs at hc <;> simp_all

/-- Actual final-game class, including every padded old/old answer. -/
theorem preGame_class_zero {P : Presentation} (R : StructuralRealization P) :
    classContribution P (finalStrategy R) .preGame=0 := by
  apply class_zero_of_annihilates
  intro x y a b hc hz k hk
  obtain ⟨ox,oy,hx,hy⟩ := preGame_decoded P x y a b hc
  have hk' : 0<(CompilerHonestRefinementsCorrect.strategy R).weight k :=
    lt_of_le_of_ne ((CompilerHonestRefinementsCorrect.strategy R).weight_nonneg k) (Ne.symm hk)
  exact old_old_zero (preGame P) (rows P) (CompilerHonestRefinementsCorrect.strategy R)
    (CompilerHonestPregameCorrect.perfect R)
    (CompilerHonestRefinementsCorrect.namedBinaryProjections R)
    (aliceNames R) (bobNames R) (aliceNames_projective R) (bobNames_projective R)
    x y a b ox oy hx hy hz k hk'

#print axioms preGame_class_zero
end Sigma2.CompilerHonestPregameClass
