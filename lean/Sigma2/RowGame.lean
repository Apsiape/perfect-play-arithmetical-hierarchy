import Sigma2.RowSlots

/-! The finite Boolean row-extension game, computed from G and R.
The scalar-pair contexts use all perpendicular parity checks rather than a
chosen basis of j-perp. This redundant presentation avoids a basis oracle.
All rows use one common power-of-four dimension. -/
open scoped BigOperators
namespace Sigma2.RowGame
open Compiler RowSlots

inductive Question (n m r : ℕ) where
  | anchor
  | cell (g : Fin r) (x y : Fin 3)
  | line (g : Fin r) (column : Bool) (k : Fin 3)
  | cross (g h : Fin r) (k l : Fin 4)
  | oldAxis (i : Fin n) (g : Fin r) (k : Fin 4)
  | global (isX : Bool)
  | pair (j : ℕ)
  | slot (row : Fin m) (j : ℕ)
  | column (row : Fin m)
  deriving DecidableEq, Repr

abbrev Q {s} (R : Rows s) := Question R.count R.rowCount (squares R)

def axis {s} (R : Rows s) (g : Fin (squares R)) (k : Fin 4) : Q R :=
  if k=0 then .cell g 0 0 else if k=1 then .cell g 1 0
  else if k=2 then .cell g 1 1 else .cell g 0 1

def questions {s} (R : Rows s) : List (Q R) :=
  [.anchor] ++
  (List.finRange (squares R)).flatMap (fun g =>
    (List.finRange 3).flatMap (fun x => (List.finRange 3).map (fun y => .cell g x y))) ++
  (List.finRange (squares R)).flatMap (fun g =>
    [false,true].flatMap (fun col => (List.finRange 3).map (fun k => .line g col k))) ++
  (List.finRange (squares R)).flatMap (fun g =>
    (List.finRange (squares R)).flatMap (fun h =>
      (List.finRange 4).flatMap (fun k => (List.finRange 4).map (fun l => .cross g h k l)))) ++
  (List.finRange R.count).flatMap (fun i =>
    (List.finRange (squares R)).flatMap (fun g =>
      (List.finRange 4).map (fun k => .oldAxis i g k))) ++
  [.global false, .global true] ++
  ((List.range (dimension R)).drop 1).map Question.pair ++
  (List.finRange R.rowCount).flatMap (fun r =>
    ((List.range (dimension R)).drop 1).map (fun j => .slot r j)) ++
  (List.finRange R.rowCount).map Question.column

/-- Sign bit of the F2 dot product. True means the negative character. -/
def parity (bits mask value : ℕ) : Bool :=
  (List.range bits).foldl (fun b k => Bool.xor b
    (Nat.testBit mask k && Nat.testBit value k)) false

/-- Scalar-pair outcomes consist of a sign and a canonical representative
of a coset of {0,j}. Duplicate representatives are invalid answers. -/
def valid {s} (R : Rows s) (q : Q R) (a : ℕ) : Bool :=
  match q with
  | .anchor => decide (a=1)
  | .cell .. => decide (a<2)
  | .line .. => decide (a<4)
  | .cross g h .. => if g=h then decide (a=0) else decide (a<4)
  | .oldAxis .. => decide (a<4)
  | .global _ => decide (a<dimension R)
  | .pair j => decide (a<2*dimension R ∧ a/2 ≤ Nat.xor (a/2) j)
  | .slot .. => decide (a<6)
  | .column _ => decide (a<dimension R)

def scalarClass (a : ℕ) : ℕ := if a/2=0 then a%2 else 2

def bitAnswer (negative : Bool) : ℕ := if negative then 0 else 1

/-- One orientation of all new/new constraints. `newRule` also applies its
transpose, so each binding and forbidden event is tested in both orientations. -/
def directed {s} (R : Rows s) (q p : Q R) (a b : ℕ) : Bool :=
  match q with
  | .line g col k =>
      (List.finRange 3).all (fun j =>
        let cell : Q R := if col then .cell g j k else .cell g k j
        if p=cell then decide (b=bitAnswer (cellSign (col && decide (k.val=2)) a j.val))
        else true)
  | .cross g h k l =>
      if g=h then true else
        (if p=axis R g k then decide (b=a/2) else true) &&
        (if p=axis R h l then decide (b=a%2) else true)
  | .oldAxis _ g k => if p=axis R g k then decide (b=a%2) else true
  | .global isX =>
      (List.finRange (squares R)).all (fun g =>
        (List.finRange 2).all (fun k =>
          let ax : Fin 4 := ⟨k.val + if isX then 2 else 0, by split <;> omega⟩
          if p=axis R g ax then decide (b=bitAnswer (Nat.testBit a (2*g.val+k.val))) else true))
  | .pair j =>
      (if p=.global true then decide (decide (a%2=1)=parity (2*squares R) j b) else true) &&
      (if p=.global false then
        (List.range (dimension R)).all (fun ell =>
          if parity (2*squares R) ell j then true else
            decide (parity (2*squares R) ell (a/2)=parity (2*squares R) ell b))
       else true)
  | .slot r j =>
      (if p=.pair j then decide (a%3=scalarClass b) else true) &&
      (match (RowSlots.slot R r j).event with
       | none => if p=.anchor then decide (a/3=b) else true
       | some _ => true)
  | .column r =>
      (if p=.global true then !(decide (a=0) && decide (b=0)) else true) &&
      ((List.range (dimension R)).drop 1).all (fun j =>
        if p=.slot r j then
          if b%3=2 then true else
            let vneg := Bool.xor (decide (b/3=0)) (RowSlots.slot R r j).negative
            decide (Bool.xor (decide (b%3=1)) vneg=parity (2*squares R) a j)
        else true)
  | _ => true

def newRule {s} (R : Rows s) (q p : Q R) (a b : ℕ) : Bool :=
  valid R q a && valid R p b &&
    (if q=p then decide (a=b) else true) && directed R q p a b && directed R p q b a

/-- New-to-old marginal bindings, with old synchronized events coarsened to
one binary answer and its complement. Old nonsynchronous questions stay intact. -/
def bindOldA {s} (R : Rows s) (x : QA s) (q : Q R) (a b : ℕ) : Bool :=
  match q with
  | .oldAxis i .. =>
      if x=(R.event i).x then decide ((a=(R.event i).a.val) ↔ b/2=1) else true
  | .slot r j =>
      match (RowSlots.slot R r j).event with
      | none => decide (b/3=1)
      | some i => if x=(R.event i).x then decide ((a=(R.event i).a.val) ↔ b/3=1) else true
  | _ => true

def bindOldB {s} (R : Rows s) (q : Q R) (y : QB s) (a b : ℕ) : Bool :=
  match q with
  | .oldAxis i .. =>
      if y=(R.event i).y then decide ((b=(R.event i).b.val) ↔ a/2=1) else true
  | .slot r j =>
      match (RowSlots.slot R r j).event with
      | none => decide (a/3=1)
      | some i => if y=(R.event i).y then decide ((b=(R.event i).b.val) ↔ a/3=1) else true
  | _ => true

def scenario (G : Game) (R : Rows G.scenario) : Scenario where
  questionsA := G.scenario.questionsA + (questions R).length
  questionsB := G.scenario.questionsB + (questions R).length
  answersA := G.scenario.answersA + G.scenario.answersB + 2*dimension R + 6
  answersB := G.scenario.answersA + G.scenario.answersB + 2*dimension R + 6

def embedding (G : Game) (R : Rows G.scenario) : ScenarioEmbedding G.scenario (scenario G R) where
  qA x := ⟨x.val, by have := x.isLt; dsimp [scenario]; omega⟩
  qB y := ⟨y.val, by have := y.isLt; dsimp [scenario]; omega⟩
  aA a := ⟨a.val, by have := a.isLt; dsimp [scenario]; omega⟩
  aB b := ⟨b.val, by have := b.isLt; dsimp [scenario]; omega⟩
  iqA := by intro x y h; exact Fin.ext (congrArg (fun z : QA (scenario G R) => z.val) h)
  iqB := by intro x y h; exact Fin.ext (congrArg (fun z : QB (scenario G R) => z.val) h)
  iaA := by intro x y h; exact Fin.ext (congrArg (fun z : AA (scenario G R) => z.val) h)
  iaB := by intro x y h; exact Fin.ext (congrArg (fun z : BB (scenario G R) => z.val) h)

def decodeA (G : Game) (R : Rows G.scenario) (x : QA (scenario G R)) : QA G.scenario ⊕ Q R :=
  if h : x.val < G.scenario.questionsA+1 then .inl ⟨x.val,h⟩
  else .inr ((questions R)[x.val-(G.scenario.questionsA+1)]?.getD .anchor)

def decodeB (G : Game) (R : Rows G.scenario) (y : QB (scenario G R)) : QB G.scenario ⊕ Q R :=
  if h : y.val < G.scenario.questionsB+1 then .inl ⟨y.val,h⟩
  else .inr ((questions R)[y.val-(G.scenario.questionsB+1)]?.getD .anchor)

def oldSync {s} (R : Rows s) (x : QA s) (y : QB s) (a b : ℕ) : Bool :=
  (List.finRange R.count).all (fun i =>
    if x=(R.event i).x ∧ y=(R.event i).y then
      decide (a=(R.event i).a.val ↔ b=(R.event i).b.val) else true)

def accepts (G : Game) (R : Rows G.scenario)
    (x : QA (scenario G R)) (y : QB (scenario G R))
    (a : AA (scenario G R)) (b : BB (scenario G R)) : Bool :=
  match decodeA G R x, decodeB G R y with
  | .inl x, .inl y =>
      if ha : a.val<G.scenario.answersA+1 then
        if hb : b.val<G.scenario.answersB+1 then
          (if G.distribution x y=0 then true else G.accepts x y ⟨a.val,ha⟩ ⟨b.val,hb⟩) &&
          oldSync R x y a.val b.val
        else false
      else false
  | .inl x, .inr p => decide (a.val<G.scenario.answersA+1) && valid R p b.val &&
      bindOldA R x p a.val b.val
  | .inr q, .inl y => valid R q a.val && decide (b.val<G.scenario.answersB+1) &&
      bindOldB R q y a.val b.val
  | .inr q, .inr p => newRule R q p a.val b.val

def game (G : Game) (R : Rows G.scenario) : Game where
  scenario := scenario G R
  distribution := fun _ _ => 1 / (((scenario G R).questionsA+1 : ℕ) *
    ((scenario G R).questionsB+1 : ℕ) : ℕ)
  distribution_nonneg := by intro x y; positivity
  distribution_sum := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  accepts := accepts G R

theorem distribution_positive (G : Game) (R : Rows G.scenario) (x y) :
    0 < (game G R).distribution x y := by dsimp [game]; positivity

theorem decodeA_old (G : Game) (R : Rows G.scenario) (x : QA G.scenario) :
    decodeA G R ((embedding G R).qA x)=.inl x := by
  simp [decodeA, embedding, x.isLt]

theorem decodeB_old (G : Game) (R : Rows G.scenario) (y : QB G.scenario) :
    decodeB G R ((embedding G R).qB y)=.inl y := by
  simp [decodeB, embedding, y.isLt]

/-- Every originally sampled losing event is still rejected, regardless of
how many names refer to that original question pair. -/
theorem retains_losing (G : Game) (R : Rows G.scenario) (x y a b)
    (hd : G.distribution x y ≠ 0) (hl : G.accepts x y a b=false) :
    (game G R).accepts ((embedding G R).qA x) ((embedding G R).qB y)
      ((embedding G R).aA a) ((embedding G R).aB b)=false := by
  change accepts G R _ _ _ _=false
  simp only [accepts, decodeA_old, decodeB_old]
  simp [embedding, a.isLt, b.isLt, hd, hl]

/-- Full-support sampling turns every concrete Boolean rejection into an
actual zero probability. This is the first soundness step for this game. -/
theorem rejected_probability (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (x y a b) (h : (game G R).accepts x y a b=false) : S.probability x y a b=0 := by
  change loss (game G R) S=0 at hS
  have hh := Preliminaries.losing_event_le_loss (game G R) S x y a b
  simp only [h, Bool.false_eq_true, ite_false, hS] at hh
  have hd : (0:ℝ)<((game G R).distribution x y:ℝ) := by
    exact_mod_cast distribution_positive G R x y
  have hn := Preliminaries.probability_nonnegative S x y a b
  apply le_antisymm _ hn
  by_contra hp
  exact (not_lt_of_ge hh) (mul_pos hd (lt_of_not_ge hp))

#print axioms game
#print axioms retains_losing
#print axioms rejected_probability
end Sigma2.RowGame





