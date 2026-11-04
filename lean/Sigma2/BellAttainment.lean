import Sigma2.Preliminaries

noncomputable section
open scoped BigOperators ComplexOrder
namespace Sigma2.BellAttainment

def absoluteSum (L : Bell) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, |(L.coefficients x y a b : ℝ)|

def Stage (L : Bell) (κ n : ℕ) (β : ℝ) : Prop :=
  ∃ (d : Fin (n+1) → ℝ)
    (E : QA L.scenario → AA L.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (F : QB L.scenario → BB L.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ),
    d 0=1 ∧ (∀ i, 0 ≤ d i) ∧ Antitone d ∧ (∑ i, d i^2) ≤ κ ∧
    (∀ x a, (E x a).PosSemidef) ∧ (∀ y b, (F y b).PosSemidef) ∧
    (∀ x, ∑ a, E x a=1) ∧ (∀ y, ∑ b, F y b=1) ∧
    ∀ i j,
      ‖((∑ x, ∑ y, ∑ a, ∑ b,
          (L.coefficients x y a b:ℂ) • (E x a*Matrix.diagonal (fun k => (d k:ℂ))*(F y b).transpose))-
        (β:ℂ) • Matrix.diagonal (fun k => (d k:ℂ))) i j‖^2 ≤
          absoluteSum L ^ 2 * κ/(n+2)

def DimensionBound (L : Bell) (n : ℕ) (β : ℝ) : Prop :=
  ∀ (ρ : Matrix (Fin (n+1) × Fin (n+1)) (Fin (n+1) × Fin (n+1)) ℂ)
    (E : QA L.scenario → AA L.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (F : QB L.scenario → BB L.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ),
    ρ.PosSemidef → (∑ i, ρ i i)=1 →
    (∀ x a, (E x a).PosSemidef) → (∀ y b, (F y b).PosSemidef) →
    (∀ x, ∑ a, E x a=1) → (∀ y, ∑ b, F y b=1) →
    (∑ x, ∑ y, ∑ a, ∑ b, (L.coefficients x y a b:ℝ)*
      (∑ i, ∑ j, ρ i j*E x a j.1 i.1*F y b j.2 i.2).re) ≤ β

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

