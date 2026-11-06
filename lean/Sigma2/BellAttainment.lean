import Sigma2.ValueOne
import Sigma2.Upper

noncomputable section
open scoped BigOperators ComplexOrder
namespace Sigma2.BellAttainment

def winningBell (G : Game) : Bell where
  scenario := G.scenario
  coefficients := fun x y a b => if G.accepts x y a b then G.distribution x y else 0

theorem winning_value (G : Game) (S : NormalStrategy G.scenario) :
    bellValue (winningBell G) S=win G S := by
  simp only [bellValue,winningBell,win]
  congr 1; funext x; congr 1; funext y; congr 1; funext a; congr 1; funext b
  split_ifs <;> simp_all

theorem winning_attainment (G : Game) : BellAttains (winningBell G) 1 ↔ HasPerfect G := by
  change (∃ S : NormalStrategy G.scenario, bellValue (winningBell G) S=1) ↔ HasPerfect G
  constructor
  · rintro ⟨S,hS⟩
    refine ⟨S,?_⟩
    unfold Perfect
    rw [Preliminaries.loss_eq_one_sub_win,← winning_value,hS,sub_self]
  · rintro ⟨S,hS⟩
    refine ⟨S,?_⟩
    rw [winning_value]
    have h := Preliminaries.loss_eq_one_sub_win G S
    change loss G S=0 at hS
    linarith

end Sigma2.BellAttainment

