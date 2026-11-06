import Sigma2.CompilerEventCounting

/-! Exact finite rejection bookkeeping, including the padded answers. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerEventLoss
open Compiler CompilerScaffold CompilerEventCounting

/-- Application rows are the final suffix of the frozen row list. -/
def applicationRow (P : Presentation) (r : Fin (rows P).rowCount) : Prop :=
  (rowList P).length - (applicationPolynomials P).length ≤ r.val

/-- The suffix length is the actual application-polynomial count. -/
theorem application_suffix_length (P : Presentation) :
    (applicationPolynomials P).length ≤ (rowList P).length := by
  simp only [rowList,polynomials,List.length_append,List.length_map]
  omega

inductive TestClass where
  | preGame | applicationForward | applicationReverse | structural
  deriving DecidableEq, Fintype

/-- Old/old is the entire padded preGame block, including oldSync. Only
zero/zero on an application column/reference pair is an application event;
all other row-extension checks, including invalid answers, are structural. -/
def testClass (P : Presentation) (x : QA (finalGame P).scenario)
    (y : QB (finalGame P).scenario) (a : AA (finalGame P).scenario)
    (b : BB (finalGame P).scenario) : TestClass := by
  classical
  exact match RowGame.decodeA (preGame P) (rows P) x,
      RowGame.decodeB (preGame P) (rows P) y with
    | .inl _, .inl _ => .preGame
    | .inr (.column r), .inr (.global true) =>
        if applicationRow P r ∧ a=0 ∧ b=0 then .applicationForward else .structural
    | .inr (.global true), .inr (.column r) =>
        if applicationRow P r ∧ a=0 ∧ b=0 then .applicationReverse else .structural
    | _, _ => .structural

/-- Conditional rejected probability; it includes the frozen Boolean table. -/
def rejection (P : Presentation) (S : NormalStrategy (finalGame P).scenario)
    (x : QA (finalGame P).scenario) (y : QB (finalGame P).scenario)
    (a : AA (finalGame P).scenario) (b : BB (finalGame P).scenario) : ℝ := if (finalGame P).accepts x y a b then 0 else S.probability x y a b

/-- An exact 1/Q² weight on every ordered pair and every rejected outcome. -/
def classContribution (P : Presentation) (S : NormalStrategy (finalGame P).scenario)
    (c : TestClass) : ℝ := by
  classical
  exact ∑ x, ∑ y, ∑ a, ∑ b,
    (1/(questionCount P:ℝ)^2) *
      (if testClass P x y a b=c then rejection P S x y a b else 0)

theorem rejection_nonnegative (P : Presentation)
    (S : NormalStrategy (finalGame P).scenario) (x y a b) :
    0 ≤ rejection P S x y a b := by
  unfold rejection
  split <;> simp_all [Preliminaries.probability_nonnegative]

theorem class_nonnegative (P : Presentation)
    (S : NormalStrategy (finalGame P).scenario) (c : TestClass) :
    0 ≤ classContribution P S c := by
  classical
  apply Finset.sum_nonneg; intro x hx
  apply Finset.sum_nonneg; intro y hy
  apply Finset.sum_nonneg; intro a ha
  apply Finset.sum_nonneg; intro b hb
  apply mul_nonneg (by positivity)
  split <;> simp_all [rejection_nonnegative]

/-- Four disjoint classes exhaust the frozen loss, without any honest-state
or perfect-structural-tests assumption. Both orientations retain full weight. -/
theorem loss_decomposition (P : Presentation)
    (S : NormalStrategy (finalGame P).scenario) :
    loss (finalGame P) S =
      classContribution P S .applicationForward +
      classContribution P S .applicationReverse +
      classContribution P S .structural + classContribution P S .preGame := by
  classical
  unfold loss classContribution
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x hx
  apply Finset.sum_congr rfl; intro y hy
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  rw [final_distribution]
  change _*rejection P S x y a b=_
  cases testClass P x y a b <;> simp

theorem class_le_loss (P : Presentation)
    (S : NormalStrategy (finalGame P).scenario) (c : TestClass) :
    classContribution P S c ≤ loss (finalGame P) S := by
  have h1 := class_nonnegative P S .applicationForward
  have h2 := class_nonnegative P S .applicationReverse
  have h3 := class_nonnegative P S .structural
  have h4 := class_nonnegative P S .preGame
  rw [loss_decomposition]
  cases c <;> linarith

/-- Annihilation is required only for occupied ensemble components. -/
theorem probability_zero_of_annihilates {s} (S : NormalStrategy s) (x y a b)
    (hz : ∀ k,S.weight k ≠ 0 →
      (S.measurements.left x a*S.measurements.right y b) (S.vector k)=0) :
    S.probability x y a b=0 := by
  unfold NormalStrategy.probability
  convert (tsum_zero : (∑' _ : ℕ,(0:ℝ))=0) using 1
  apply tsum_congr
  intro k
  by_cases hw : S.weight k=0
  · simp only [hw,zero_mul]
  · simp only [PureStrategy.probability,NormalStrategy.component,hz k hw,
      inner_zero_right,Complex.zero_re,mul_zero]

theorem class_zero_of_annihilates (P : Presentation)
    (S : NormalStrategy (finalGame P).scenario) (c : TestClass)
    (hz : ∀ x y a b,testClass P x y a b=c → (finalGame P).accepts x y a b=false →
      ∀ k,S.weight k ≠ 0 →
        (S.measurements.left x a*S.measurements.right y b) (S.vector k)=0) :
    classContribution P S c=0 := by
  classical
  unfold classContribution
  apply Finset.sum_eq_zero; intro x hx
  apply Finset.sum_eq_zero; intro y hy
  apply Finset.sum_eq_zero; intro a ha
  apply Finset.sum_eq_zero; intro b hb
  by_cases hc : testClass P x y a b=c
  · simp only [hc,ite_true,rejection]
    cases he : (finalGame P).accepts x y a b
    · simp only [Bool.false_eq_true,ite_false]
      rw [probability_zero_of_annihilates S x y a b (hz x y a b hc he),mul_zero]
    · simp
  · simp only [hc,ite_false,mul_zero]

#print axioms applicationRow
#print axioms application_suffix_length
#print axioms testClass
#print axioms rejection
#print axioms classContribution
#print axioms rejection_nonnegative
#print axioms class_nonnegative
#print axioms loss_decomposition
#print axioms class_le_loss
#print axioms probability_zero_of_annihilates
#print axioms class_zero_of_annihilates
end Sigma2.CompilerEventLoss


