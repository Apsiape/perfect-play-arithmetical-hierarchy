import Sigma2.CompilerEventLoss

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerEventClasses
open Compiler CompilerScaffold CompilerEventCounting CompilerEventLoss

/-- Each class has precisely the frozen square weight, with no orientation coin. -/
theorem class_exact_weight (P : Presentation) (S : NormalStrategy (finalGame P).scenario)
    (c : TestClass) :
    classContribution P S c=(1/(questionCount P:ℝ)^2)*
      ∑ x,∑ y,∑ a,∑ b,if testClass P x y a b=c then rejection P S x y a b else 0 := by
  classical
  unfold classContribution
  simp only [← Finset.mul_sum]

/-- In particular, forward application zero/zero really lies in its own class. -/
theorem forward_class (P : Presentation) (r : Fin (rows P).rowCount)
    (hr : applicationRow P r) :
    testClass P
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P))) 0 0=
        .applicationForward := by
  simp [testClass,RowScalar.decode_qa,RowScalar.decode_qb,columnQuestion,referenceQuestion,hr]

theorem reverse_class (P : Presentation) (r : Fin (rows P).rowCount)
    (hr : applicationRow P r) :
    testClass P
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)) 0 0=
        .applicationReverse := by
  simp [testClass,RowScalar.decode_qa,RowScalar.decode_qb,columnQuestion,referenceQuestion,hr]

/-- Every old/old pair belongs to the padded preGame block at every answer. -/
theorem preGame_class (P : Presentation) (x : QA (preGame P).scenario)
    (y : QB (preGame P).scenario) (a : AA (finalGame P).scenario)
    (b : BB (finalGame P).scenario) :
    testClass P ((RowGame.embedding (preGame P) (rows P)).qA x)
      ((RowGame.embedding (preGame P) (rows P)).qB y) a b=.preGame := by
  simp only [testClass,RowGame.decodeA_old,RowGame.decodeB_old]

/-- At each actual forward pair, the row-zero summand is p_forward/Q². -/
theorem forward_exact_weight (P : Presentation) (r : Fin (rows P).rowCount)
    (S : NormalStrategy (finalGame P).scenario) :
    ((finalGame P).distribution
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P))):ℝ)*
      rejection P S
        (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
        (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P))) 0 0=
    S.probability
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P))) 0 0 /
        (questionCount P:ℝ)^2 := by
  rw [final_distribution]
  unfold rejection
  rw [final_row_zero_rejected P r _ _ (RowScalar.decode_qa _ _ _)
    (RowScalar.decode_qb _ _ _)]
  simp only [Bool.false_eq_true,ite_false]
  ring

theorem reverse_exact_weight (P : Presentation) (r : Fin (rows P).rowCount)
    (S : NormalStrategy (finalGame P).scenario) :
    ((finalGame P).distribution
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)):ℝ)*
      rejection P S
        (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
        (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)) 0 0=
    S.probability
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)) 0 0 /
        (questionCount P:ℝ)^2 := by
  rw [final_distribution]
  unfold rejection
  rw [final_row_zero_transpose_rejected P r _ _ (RowScalar.decode_qa _ _ _)
    (RowScalar.decode_qb _ _ _)]
  simp only [Bool.false_eq_true,ite_false]
  ring

/-- When preGame and structural rejection effects kill the state, only the
TWO separately weighted application classes remain. -/
theorem loss_only_application (P : Presentation)
    (S : NormalStrategy (finalGame P).scenario)
    (hz : ∀ x y a b,
      (testClass P x y a b=.structural ∨ testClass P x y a b=.preGame) →
      (finalGame P).accepts x y a b=false → ∀ k,S.weight k≠0 →
        (S.measurements.left x a*S.measurements.right y b) (S.vector k)=0) :
    loss (finalGame P) S=classContribution P S .applicationForward+
      classContribution P S .applicationReverse := by
  rw [loss_decomposition,
    class_zero_of_annihilates P S .structural (fun x y a b hc => hz x y a b (Or.inl hc)),
    class_zero_of_annihilates P S .preGame (fun x y a b hc => hz x y a b (Or.inr hc))]
  ring

#print axioms class_exact_weight
#print axioms forward_class
#print axioms reverse_class
#print axioms preGame_class
#print axioms forward_exact_weight
#print axioms reverse_exact_weight
#print axioms loss_only_application
end Sigma2.CompilerEventClasses
