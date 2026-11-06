import Sigma2.UpperCoding
import Mathlib.Computability.Primrec.List

/-! Finite rational polynomial syntax and existential ordered-ring sentences.
A polynomial is a sum of products of rational constants and variables. -/
namespace Sigma2.UpperRealArithmetic
open scoped BigOperators

abbrev Factor := ℚ ⊕ ℕ
abbrev Poly := List (List Factor)
abbrev Atom := Bool × Poly
abbrev Sentence := List Atom

def factorEval (v : ℕ → ℝ) : Factor → ℝ := Sum.elim (fun q => (q : ℝ)) v
def eval (v : ℕ → ℝ) (p : Poly) : ℝ :=
  (p.map fun m => (m.map (factorEval v)).prod).sum

def constant (q : ℚ) : Poly := [[Sum.inl q]]
def var (n : ℕ) : Poly := [[Sum.inr n]]
def add (p q : Poly) : Poly := p ++ q
def neg (p : Poly) : Poly := p.map fun m => Sum.inl (-1) :: m
def mul (p q : Poly) : Poly := p.flatMap fun a => q.map fun b => a ++ b
def sub (p q : Poly) : Poly := add p (neg q)
def sum (ps : List Poly) : Poly := ps.flatten

def holds (v : ℕ → ℝ) (a : Atom) : Prop :=
  if a.1 then eval v a.2 = 0 else 0 ≤ eval v a.2

def Truth (s : Sentence) : Prop := ∃ v : ℕ → ℝ, ∀ a ∈ s, holds v a

/-- A literal is an atom or its negation. A sentence is an existentially
closed disjunction of conjunctions of literals (disjunctive normal form). -/
abbrev Literal := Bool × Atom
abbrev OrderedRingSentence := List (List Literal)

def literalHolds (v : ℕ → ℝ) (a : Literal) : Prop :=
  if a.1 then holds v a.2 else ¬ holds v a.2

def OrderedRingTruth (s : OrderedRingSentence) : Prop :=
  ∃ v : ℕ → ℝ, ∃ clause ∈ s, ∀ a ∈ clause, literalHolds v a

/-- Decidability of the existential theory of the reals in the explicit rational
ordered-ring syntax above. This is a special case of Tarski's 1951 decision
procedure for real closed fields, so the hypothesis is weaker than the published
theorem. It is passed as an explicit theorem argument, never an axiom. -/
def TarskiDecision : Prop := ComputablePred OrderedRingTruth

def conjunctive (s : Sentence) : OrderedRingSentence := [s.map fun a => (true,a)]

@[simp] theorem truth_conjunctive (s : Sentence) : OrderedRingTruth (conjunctive s) ↔ Truth s := by
  simp [OrderedRingTruth,conjunctive,literalHolds,Truth]

open Primrec in
theorem conjunctive_primrec : Primrec conjunctive :=
  list_cons.comp (list_map .id ((const true).pair snd).to₂) (const [])

theorem conjunction_decision (hT : TarskiDecision) : ComputablePred Truth := by
  classical
  have hh : ComputablePred (fun s => OrderedRingTruth (conjunctive s)) :=
    Computable.computablePred (hT.decide.comp conjunctive_primrec.to_comp)
  exact hh.of_eq truth_conjunctive

@[simp] theorem eval_constant (v : ℕ → ℝ) (q : ℚ) : eval v (constant q) = q := by
  simp [eval, constant, factorEval]
@[simp] theorem eval_var (v : ℕ → ℝ) (n : ℕ) : eval v (var n) = v n := by
  simp [eval, var, factorEval]
@[simp] theorem eval_add (v : ℕ → ℝ) (p q : Poly) : eval v (add p q) = eval v p + eval v q := by
  simp [eval, add]
@[simp] theorem eval_neg (v : ℕ → ℝ) (p : Poly) : eval v (neg p) = -eval v p := by
  induction p with
  | nil => simp [eval, neg]
  | cons a p ih => simp [eval, neg, factorEval] at *; rw [ih]; ring
@[simp] theorem eval_mul (v : ℕ → ℝ) (p q : Poly) : eval v (mul p q) = eval v p * eval v q := by
  have hm (a : List Factor) :
      eval v (q.map fun b => a ++ b) = (a.map (factorEval v)).prod * eval v q := by
    induction q with
    | nil => simp [eval]
    | cons b q ih => simp [eval, List.map_map, List.prod_append, mul_add] at *; rw [ih]
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih =>
    change eval v (add (q.map fun b => a ++ b) (mul p q)) = _
    rw [eval_add, hm, ih]
    simp [eval, add_mul]
@[simp] theorem eval_sub (v : ℕ → ℝ) (p q : Poly) : eval v (sub p q) = eval v p - eval v q := by
  simp [sub, sub_eq_add_neg]
@[simp] theorem eval_sum (v : ℕ → ℝ) (ps : List Poly) : eval v (sum ps) = (ps.map (eval v)).sum := by
  induction ps with
  | nil => simp [sum, eval]
  | cons p ps ih => simpa [sum, eval] using congrArg (eval v p + ·) ih

/-- The finite list of free variables; existential closure binds these. -/
def freeVars (s : Sentence) : List ℕ :=
  s.flatMap fun a => a.2.flatMap fun m => m.filterMap Sum.getRight?

theorem eval_congr (v w : ℕ → ℝ) (p : Poly)
    (h : ∀ m ∈ p, ∀ i, Sum.inr i ∈ m → v i = w i) : eval v p = eval w p := by
  unfold eval
  congr 1
  apply List.map_congr_left
  intro m hm
  congr 1
  apply List.map_congr_left
  intro t ht
  cases t with
  | inl q => rfl
  | inr i => exact h m hm i ht

/-- The semantics quantifies only finitely many real coordinates. -/
theorem truth_finite (s : Sentence) : Truth s ↔
    ∃ v : {i : ℕ // i ∈ freeVars s} → ℝ,
      ∀ a ∈ s, holds (fun i => if h : i ∈ freeVars s then v ⟨i,h⟩ else 0) a := by
  classical
  constructor
  · rintro ⟨v,hv⟩
    refine ⟨fun i => v i, ?_⟩
    intro a ha
    have he : eval (fun i => if h : i ∈ freeVars s then v i else 0) a.2 = eval v a.2 := by
      apply eval_congr
      intro m hm i hi
      have : i ∈ freeVars s := by
        simp only [freeVars, List.mem_flatMap, List.mem_filterMap]
        exact ⟨a,ha,m,hm,Sum.inr i,hi,rfl⟩
      simp [this]
    simpa only [holds,he] using hv a ha
  · rintro ⟨v,hv⟩
    exact ⟨_,hv⟩

open Primrec in
theorem constant_primrec : Primrec constant :=
  list_cons.comp (list_cons.comp Primrec.sumInl (const [])) (const [])
open Primrec in
theorem var_primrec : Primrec var :=
  list_cons.comp (list_cons.comp Primrec.sumInr (const [])) (const [])
theorem add_primrec : Primrec₂ add := Primrec.list_append
open Primrec in
theorem neg_primrec : Primrec neg :=
  list_map .id (list_cons.comp (const (Sum.inl (-1))) snd).to₂
open Primrec in
theorem mul_primrec : Primrec₂ mul :=
  (list_flatMap fst (list_map (snd.comp fst) (list_append.comp (snd.comp fst) snd).to₂).to₂).to₂
open Primrec in
theorem sub_primrec : Primrec₂ sub := add_primrec.comp fst (neg_primrec.comp snd)
theorem sum_primrec : Primrec sum := Primrec.list_flatten

end Sigma2.UpperRealArithmetic

