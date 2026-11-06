import Sigma2.CompilerScaffold
import Sigma2.RowScalar

/-! The stage 3 stop-condition audit: the frozen predicate rejects row zero
in TWO ordered question pairs, each with the full uniform square weight.
This module does not assert the unproved analytic event/trace bridge. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerEventCounting
open Compiler CompilerScaffold

/-- The actual padded final-game question count on each side. -/
def questionCount (P : Presentation) : ℕ := (finalGame P).scenario.questionsA+1

theorem final_question_square (P : Presentation) :
    (finalGame P).scenario.questionsB=(finalGame P).scenario.questionsA := rfl

theorem final_distribution (P : Presentation) (x y) :
    ((finalGame P).distribution x y : ℝ)=1/(questionCount P:ℝ)^2 := by
  change ((1 / (((finalGame P).scenario.questionsA+1)*
    ((finalGame P).scenario.questionsB+1) : ℕ) : ℚ) : ℝ)=_
  rw [final_question_square]
  push_cast
  simp only [questionCount,pow_two,Nat.cast_add,Nat.cast_one]

/-- Exactly the forbidden zero/zero outcome, in the forward orientation. -/
theorem newRule_row_zero {s} (R : Rows s) (r : Fin R.rowCount) :
    RowGame.newRule R (.column r) (.global true) 0 0=false := by
  simp [RowGame.newRule,RowGame.directed]

/-- The transpose is ALSO forbidden; there is no orientation coin. -/
theorem newRule_row_zero_transpose {s} (R : Rows s) (r : Fin R.rowCount) :
    RowGame.newRule R (.global true) (.column r) 0 0=false := by
  simp [RowGame.newRule,RowGame.directed]

/-- The same two rejections in the actual frozen final game. -/
theorem final_row_zero_rejected (P : Presentation) (r : Fin (rows P).rowCount)
    (x : QA (finalGame P).scenario) (y : QB (finalGame P).scenario)
    (hx : RowGame.decodeA (preGame P) (rows P) x=.inr (.column r))
    (hy : RowGame.decodeB (preGame P) (rows P) y=.inr (.global true)) :
    (finalGame P).accepts x y 0 0=false := by
  change RowGame.accepts (preGame P) (rows P) x y 0 0=false
  simp only [RowGame.accepts,hx,hy,Fin.val_zero]
  exact newRule_row_zero _ _

theorem final_row_zero_transpose_rejected (P : Presentation) (r : Fin (rows P).rowCount)
    (x : QA (finalGame P).scenario) (y : QB (finalGame P).scenario)
    (hx : RowGame.decodeA (preGame P) (rows P) x=.inr (.global true))
    (hy : RowGame.decodeB (preGame P) (rows P) y=.inr (.column r)) :
    (finalGame P).accepts x y 0 0=false := by
  change RowGame.accepts (preGame P) (rows P) x y 0 0=false
  simp only [RowGame.accepts,hx,hy,Fin.val_zero]
  exact newRule_row_zero_transpose _ _

/-- Two actual summands of `loss`, including their frozen distribution weights.
The four indices are supplied with their actual decoder equalities below. -/
def bothZeroContribution (P : Presentation) (S : NormalStrategy (finalGame P).scenario)
    (xc xx : QA (finalGame P).scenario) (yx yc : QB (finalGame P).scenario) : ℝ :=
  ((finalGame P).distribution xc yx:ℝ)*
    (if (finalGame P).accepts xc yx 0 0 then 0 else S.probability xc yx 0 0)+
  ((finalGame P).distribution xx yc:ℝ)*
    (if (finalGame P).accepts xx yc 0 0 then 0 else S.probability xx yc 0 0)

/-- Even after granting equal per-orientation probability p, the combined
contribution is 2p/Q^2, not p/Q^2. No state construction is assumed here. -/
theorem both_zero_weight (P : Presentation) (r : Fin (rows P).rowCount)
    (S : NormalStrategy (finalGame P).scenario)
    (xc xx : QA (finalGame P).scenario) (yx yc : QB (finalGame P).scenario)
    (hxc : RowGame.decodeA (preGame P) (rows P) xc=.inr (.column r))
    (hxx : RowGame.decodeA (preGame P) (rows P) xx=.inr (.global true))
    (hyx : RowGame.decodeB (preGame P) (rows P) yx=.inr (.global true))
    (hyc : RowGame.decodeB (preGame P) (rows P) yc=.inr (.column r))
    (p : ℝ) (hp : S.probability xc yx 0 0=p) (hp' : S.probability xx yc 0 0=p) :
    bothZeroContribution P S xc xx yx yc=2*p/(questionCount P:ℝ)^2 := by
  unfold bothZeroContribution
  rw [final_row_zero_rejected P r xc yx hxc hyx,
    final_row_zero_transpose_rejected P r xx yc hxx hyc]
  simp only [Bool.false_eq_true,ite_false,final_distribution,hp,hp']
  ring

/-- The exact algebraic doubling of the existing frozen row_loss_formula.
This does not claim to derive per-orientation probabilities from measurements. -/
theorem doubled_row_loss_formula (L d : ℕ) (hd : 0<d) (A : Op) (hA : star A=A)
    (h : Density) (hc : Centralizes h.op A)
    (V : Fin d → Op) (hV : ∀ j,Unitary (V j))
    (hv : ∑ j,V j=(2*(L:ℂ)) • A) (Q : ℝ) :
    2*((1/(d:ℝ)^3)*(trace (h.op*(star (∑ j,V j)*(∑ j,V j)))).re)/Q^2=
      8*(L:ℝ)^2/(d:ℝ)^3/Q^2*(trace (h.op*(A*A))).re := by
  rw [Compiler.row_loss_formula L d hd A hA h hc V hV hv]
  ring

/-- Both named questions really occur in the frozen question list. -/
def columnQuestion {s} (R : Rows s) (r : Fin R.rowCount) : RowScalar.NewQ R :=
  ⟨.column r,by simp [RowGame.questions,List.mem_map]⟩

def referenceQuestion {s} (R : Rows s) : RowScalar.NewQ R :=
  ⟨.global true,by simp [RowGame.questions]⟩

/-- The two ordered question pairs are distinct actual indices. -/
theorem question_indices_distinct (G : Game) (R : Rows G.scenario) (r : Fin R.rowCount) :
    RowScalar.qa G R (columnQuestion R r) ≠ RowScalar.qa G R (referenceQuestion R) := by
  intro he
  have hd := congrArg (RowGame.decodeA G R) he
  simp only [RowScalar.decode_qa,columnQuestion,referenceQuestion] at hd
  cases hd

/-- Concrete instantiation at frozen question indices: no decoder hypotheses
are left to the caller. Only the two numerical probabilities are supplied. -/
theorem actual_both_zero_weight (P : Presentation) (r : Fin (rows P).rowCount)
    (S : NormalStrategy (finalGame P).scenario) (p : ℝ)
    (hp : S.probability
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P))) 0 0=p)
    (hp' : S.probability
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)) 0 0=p) :
    bothZeroContribution P S
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r))=
        2*p/(questionCount P:ℝ)^2 := by
  apply both_zero_weight P r S _ _ _ _ _ _ _ _ p hp hp'
  · exact RowScalar.decode_qa (preGame P) (rows P) (columnQuestion (rows P) r)
  · exact RowScalar.decode_qa (preGame P) (rows P) (referenceQuestion (rows P))
  · exact RowScalar.decode_qb (preGame P) (rows P) (referenceQuestion (rows P))
  · exact RowScalar.decode_qb (preGame P) (rows P) (columnQuestion (rows P) r)

/-- The single-orientation coefficient cannot equal its doubled contribution
at positive probability. -/
theorem doubled_weight_ne_single (p Q : ℝ) (hp : 0<p) (hQ : Q≠0) :
    2*p/Q^2 ≠ p/Q^2 := by
  intro he
  have hq : Q^2≠0 := pow_ne_zero 2 hQ
  have hh := (div_left_inj' hq).mp he
  linarith

#print axioms columnQuestion
#print axioms referenceQuestion
#print axioms question_indices_distinct
#print axioms actual_both_zero_weight
#print axioms doubled_weight_ne_single
#print axioms questionCount
#print axioms final_question_square
#print axioms final_distribution
#print axioms newRule_row_zero
#print axioms newRule_row_zero_transpose
#print axioms final_row_zero_rejected
#print axioms final_row_zero_transpose_rejected
#print axioms bothZeroContribution
#print axioms both_zero_weight
#print axioms doubled_row_loss_formula
end Sigma2.CompilerEventCounting


