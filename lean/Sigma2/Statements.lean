import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Computability.Reduce
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Tactic

/-!
Concrete, admission-free statements. AB is the completed Hilbert tensor product in
coordinates, not the algebraic tensor product. Tensor lifts carry their defining
coordinate equations; their existence and uniqueness are obligations in Preliminaries.
A normal state is a countable ensemble of unit vectors with summable probability
weights. This is the spectral/nuclear model of a positive trace-class density.
No computability claim is replaced by classical decidability.
-/
noncomputable section
open scoped BigOperators InnerProductSpace ComplexConjugate
namespace Sigma2

abbrev H := lp (fun _ : ℕ => ℂ) 2
abbrev AB := lp (fun _ : ℕ × ℕ => ℂ) 2
abbrev Op := H →L[ℂ] H
abbrev BipOp := AB →L[ℂ] AB

def basis (i : ℕ) : H := lp.single 2 i 1
def entry (T : Op) (i j : ℕ) : ℂ := (T (basis j)) i

def Positive (T : Op) : Prop := T.IsPositive
def Projection (T : Op) : Prop := star T = T ∧ T * T = T
def Unitary (T : Op) : Prop := star T * T = 1 ∧ T * star T = 1
def Contraction (T : Op) : Prop := ‖T‖ ≤ 1
def PositiveContraction (T : Op) : Prop := Positive T ∧ Positive (1-T)
def Centralizes (h T : Op) : Prop := h * T = T * h

def trace (T : Op) : ℂ := ∑' i, entry T i i

structure Density where
  op : Op
  positive : Positive op
  diagonal_summable : Summable (fun i => (entry op i i).re)
  trace_one : (∑' i, (entry op i i).re) = 1

def Faithful (h : Density) : Prop := Function.Injective h.op

def entropyTerm (p : ℝ) : ℝ := -p * Real.log p / Real.log 2

def FiniteDensityEntropy (h : Density) : Prop :=
  ∃ (p : ℕ → ℝ) (u : ℕ → H),
    (∀ i, 0 ≤ p i) ∧ Summable p ∧ (∑' i, p i) = 1 ∧
    Orthonormal ℂ u ∧
    (∀ v, h.op v = ∑' i, ((p i : ℂ) * inner ℂ (u i) v) • u i) ∧
    Summable (fun i => entropyTerm (p i))

structure Scenario where
  questionsA : ℕ
  questionsB : ℕ
  answersA : ℕ
  answersB : ℕ
  deriving DecidableEq, Repr, Encodable

abbrev QA (s : Scenario) := Fin (s.questionsA+1)
abbrev QB (s : Scenario) := Fin (s.questionsB+1)
abbrev AA (s : Scenario) := Fin (s.answersA+1)
abbrev BB (s : Scenario) := Fin (s.answersB+1)

structure Game where
  scenario : Scenario
  distribution : QA scenario → QB scenario → ℚ
  distribution_nonneg : ∀ x y, 0 ≤ distribution x y
  distribution_sum : ∑ x, ∑ y, distribution x y = 1
  accepts : QA scenario → QB scenario → AA scenario → BB scenario → Bool

/-- Actual local POVMs, with the unique bounded lifts to l2(N x N).
The positivity and commutation certificates are standard tensor-lift facts,
not application equations or unproved paper hypotheses. -/
structure Measurements (s : Scenario) where
  alice : QA s → AA s → Op
  bob : QB s → BB s → Op
  alice_pos : ∀ x a, Positive (alice x a)
  bob_pos : ∀ y b, Positive (bob y b)
  alice_sum : ∀ x, ∑ a, alice x a = 1
  bob_sum : ∀ y, ∑ b, bob y b = 1
  left : QA s → AA s → BipOp
  right : QB s → BB s → BipOp
  left_coordinates : ∀ x a v i j,
    (left x a v) (i,j) = ∑' k, entry (alice x a) i k * v (k,j)
  right_coordinates : ∀ y b v i j,
    (right y b v) (i,j) = ∑' k, entry (bob y b) j k * v (i,k)
  left_sum : ∀ x, ∑ a, left x a = 1
  right_sum : ∀ y, ∑ b, right y b = 1
  commute : ∀ x y a b, left x a * right y b = right y b * left x a
  joint_positive : ∀ x y a b, (left x a * right y b).IsPositive

structure PureStrategy (s : Scenario) where
  measurements : Measurements s
  vector : AB
  unit : ‖vector‖ = 1

/-- Countable ensembles represent precisely normal (trace-class) states.
All components share the queried measurements. Orthogonality is unnecessary. -/
structure NormalStrategy (s : Scenario) where
  measurements : Measurements s
  vector : ℕ → AB
  unit : ∀ k, ‖vector k‖ = 1
  weight : ℕ → ℝ
  weight_nonneg : ∀ k, 0 ≤ weight k
  weight_summable : Summable weight
  weight_sum : (∑' k, weight k) = 1

def PureStrategy.probability {s} (S : PureStrategy s) (x : QA s) (y : QB s)
    (a : AA s) (b : BB s) : ℝ :=
  (inner ℂ S.vector ((S.measurements.left x a * S.measurements.right y b) S.vector)).re

def NormalStrategy.component {s} (S : NormalStrategy s) (k : ℕ) : PureStrategy s :=
  ⟨S.measurements, S.vector k, S.unit k⟩

def NormalStrategy.probability {s} (S : NormalStrategy s) (x : QA s) (y : QB s)
    (a : AA s) (b : BB s) : ℝ :=
  ∑' k, S.weight k * (S.component k).probability x y a b

def normalOfPure {s} (S : PureStrategy s) : NormalStrategy s where
  measurements := S.measurements
  vector := fun _ => S.vector
  unit := fun _ => S.unit
  weight := fun k => if k = 0 then 1 else 0
  weight_nonneg := by intro k; split_ifs <;> norm_num
  weight_summable := by simpa using ((hasSum_ite_eq 0 (1 : ℝ)).summable)
  weight_sum := by simp

/-- Explicit unit-vector -> normal-density representation equivalence on events.
The converse, including local environment absorption, is Preliminaries.purification. -/
theorem normalOfPure_probability {s} (S : PureStrategy s) (x y a b) :
    (normalOfPure S).probability x y a b = S.probability x y a b := by
  simp [NormalStrategy.probability, normalOfPure, NormalStrategy.component]

/-- The explicit normal-state / purified-vector equivalence interface.
Its proof is `Preliminaries.purified_model_equivalence`; environment absorption
is an analytic blueprint obligation, not an extra caller-supplied hypothesis. -/
def PurifiedModelEquivalence : Prop := ∀ s : Scenario,
  (∀ S : NormalStrategy s,∃ T : PureStrategy s,∀ x y a b,
    S.probability x y a b=T.probability x y a b) ∧
  (∀ T : PureStrategy s,∃ S : NormalStrategy s,∀ x y a b,
    S.probability x y a b=T.probability x y a b)

def win (G : Game) (S : NormalStrategy G.scenario) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    (G.distribution x y : ℝ) * (if G.accepts x y a b then S.probability x y a b else 0)

def loss (G : Game) (S : NormalStrategy G.scenario) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b,
    (G.distribution x y : ℝ) * (if G.accepts x y a b then 0 else S.probability x y a b)

def Perfect (G : Game) (S : NormalStrategy G.scenario) : Prop := loss G S = 0

def MarginalA {s} (S : NormalStrategy s) (h : Density) : Prop :=
  ∀ i j, entry h.op i j = ∑' k, (S.weight k : ℂ) *
    ∑' b, S.vector k (i,b) * star (S.vector k (j,b))
def MarginalB {s} (S : NormalStrategy s) (h : Density) : Prop :=
  ∀ i j, entry h.op i j = ∑' k, (S.weight k : ℂ) *
    ∑' a, S.vector k (a,i) * star (S.vector k (a,j))

def FiniteMarginalEntropy {s} (S : NormalStrategy s) : Prop :=
  ∃ hA hB : Density, MarginalA S hA ∧ MarginalB S hB ∧
    FiniteDensityEntropy hA ∧ FiniteDensityEntropy hB

def HasPerfect (G : Game) : Prop := ∃ S, Perfect G S
def HasFiniteEntropyPerfect (G : Game) : Prop :=
  ∃ S, Perfect G S ∧ FiniteMarginalEntropy S

def FiniteSupport {s} (S : PureStrategy s) (d : ℕ) : Prop :=
  ∀ i j, d ≤ i ∨ d ≤ j → S.vector (i,j) = 0

def HasFinitePerfect (G : Game) : Prop :=
  ∃ (S : PureStrategy G.scenario) (d : ℕ), 0 < d ∧ FiniteSupport S d ∧
    Perfect G (normalOfPure S)

/-- A value is a supremum: this epsilon definition avoids an arbitrary sSup of an empty set. -/
def ValueOne (G : Game) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (S : PureStrategy G.scenario) (d : ℕ),
    0 < d ∧ FiniteSupport S d ∧ loss G (normalOfPure S) < ε

def productOverlap (v : AB) (u w : H) : ℂ :=
  ∑' ij : ℕ × ℕ, star (u ij.1 * w ij.2) * v ij

def largestSchmidt (v : AB) : ℝ :=
  sSup {p : ℝ | ∃ u w : H, ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ p = ‖productOverlap v u w‖^2}

def Stratum (G : Game) (κ : ℕ) : Prop :=
  0 < κ ∧ ∃ S : PureStrategy G.scenario,
    Perfect G (normalOfPure S) ∧ 1/(κ : ℝ) ≤ largestSchmidt S.vector

/-- Explicit finite game table. The four natural fields are counts minus one. -/
abbrev RawGame := Scenario × List ℚ × List Bool

def rawDistribution (r : RawGame) (x : QA r.1) (y : QB r.1) : ℚ :=
  r.2.1[x.val * (r.1.questionsB+1) + y.val]?.getD 0

def rawAccepts (r : RawGame) (x : QA r.1) (y : QB r.1)
    (a : AA r.1) (b : BB r.1) : Bool :=
  r.2.2[(((x.val * (r.1.questionsB+1) + y.val) * (r.1.answersA+1) + a.val) *
    (r.1.answersB+1) + b.val)]?.getD false

def ValidRawGame (r : RawGame) : Prop :=
  r.2.1.length = (r.1.questionsA+1)*(r.1.questionsB+1) ∧
  r.2.2.length = (r.1.questionsA+1)*(r.1.questionsB+1)*
    (r.1.answersA+1)*(r.1.answersB+1) ∧
  (∀ x y, 0 ≤ rawDistribution r x y) ∧
  (∑ x, ∑ y, rawDistribution r x y) = 1

instance (r : RawGame) : Decidable (ValidRawGame r) := by
  unfold ValidRawGame; infer_instance

def gameOfRaw (r : RawGame) (h : ValidRawGame r) : Game :=
  ⟨r.1, rawDistribution r, h.2.2.1, h.2.2.2, rawAccepts r⟩

def decodeGame (c : ℕ) : Option Game := do
  let r ← Encodable.decode (α := RawGame) c
  if h : ValidRawGame r then some (gameOfRaw r h) else none

def GameProperty (P : Game → Prop) (c : ℕ) : Prop := ∃ G, decodeGame c = some G ∧ P G

def SpatialPerfect : ℕ → Prop := GameProperty HasPerfect
def EntropyPerfect : ℕ → Prop := GameProperty HasFiniteEntropyPerfect
def FinitePerfect : ℕ → Prop := GameProperty HasFinitePerfect
def PromisedGame : ℕ → Prop := GameProperty (fun G => ValueOne G ∧ ¬ HasFinitePerfect G)
def CodeStratum (c κ : ℕ) : Prop := GameProperty (fun G => Stratum G κ) c

/-- The relation is a Mathlib-computable Boolean function, not merely decidable in Lean. -/
def SigmaTwo (S : ℕ → Prop) : Prop :=
  ∃ R : ℕ × ℕ × ℕ → Bool, Computable R ∧ ∀ e, S e ↔ ∃ n, ∀ t, R (e,n,t) = true

def PiOne {α : Type} [Primcodable α] (S : α → Prop) : Prop :=
  ∃ R : α × ℕ → Bool, Computable R ∧ ∀ e, S e ↔ ∀ t, R (e,t) = true

def SigmaTwoHard (P : ℕ → Prop) : Prop := ∀ S, SigmaTwo S → S ≤₀ P
def SigmaTwoComplete (P : ℕ → Prop) : Prop := SigmaTwo P ∧ SigmaTwoHard P

def PromiseHard (P D : ℕ → Prop) : Prop :=
  ∀ S, SigmaTwo S → ∃ f : ℕ → ℕ, Computable f ∧
    (∀ e, D (f e)) ∧ (∀ e, S e ↔ P (f e))

structure Bell where
  scenario : Scenario
  coefficients : QA scenario → QB scenario → AA scenario → BB scenario → ℚ

def bellValue (L : Bell) (S : NormalStrategy L.scenario) : ℝ :=
  ∑ x, ∑ y, ∑ a, ∑ b, (L.coefficients x y a b : ℝ) * S.probability x y a b

def BellBound (L : Bell) (β : ℝ) : Prop := ∀ S, bellValue L S ≤ β
def BellAttains (L : Bell) (β : ℝ) : Prop := ∃ S, bellValue L S = β
def BellSupAttains (L : Bell) : Prop := ∃ S, ∀ T, bellValue L T ≤ bellValue L S

abbrev RawBell := Scenario × List ℚ

def bellOfRaw (r : RawBell) : Bell where
  scenario := r.1
  coefficients := fun x y a b => r.2[(((x.val*(r.1.questionsB+1)+y.val)*
    (r.1.answersA+1)+a.val)*(r.1.answersB+1)+b.val)]?.getD 0

def decodeBell (c : ℕ) : Option Bell := (Encodable.decode (α := RawBell) c).map bellOfRaw

def decodeBellQuery (c : ℕ) : Option (Bell × ℚ) :=
  (Encodable.decode (α := RawBell × ℚ) c).map (fun r => (bellOfRaw r.1,r.2))

def BellValidBoundCode (c : ℕ) : Prop :=
  ∃ L β, decodeBellQuery c = some (L,β) ∧ BellBound L (β : ℝ)
def BellBoundAttainment (c : ℕ) : Prop :=
  ∃ L β, decodeBellQuery c = some (L,β) ∧ BellBound L (β : ℝ) ∧ BellAttains L (β : ℝ)
def BellSupAttainment (c : ℕ) : Prop :=
  ∃ L, decodeBell c = some L ∧ BellSupAttains L
def BellScalarAttainment (c : ℕ) : Prop :=
  ∃ L t, decodeBellQuery c = some (L,t) ∧ BellAttains L (t : ℝ)

/-- Introduction, Theorem A, including both promise hardness clauses. -/
def TheoremAStatement : Prop :=
  SigmaTwoComplete SpatialPerfect ∧ SigmaTwoComplete EntropyPerfect ∧
  PromiseHard SpatialPerfect PromisedGame ∧ PromiseHard EntropyPerfect PromisedGame

/-- Introduction, Theorem B. Supplied valid bounds also form a promise problem. -/
def TheoremBStatement : Prop :=
  SigmaTwoComplete BellBoundAttainment ∧ SigmaTwoComplete BellSupAttainment ∧
  SigmaTwoComplete BellScalarAttainment ∧
  PromiseHard BellBoundAttainment BellValidBoundCode

/-- Introduction, Theorem C; positive strata are uniform in the code and κ. -/
def TheoremCStatement : Prop :=
  PiOne (fun ek : ℕ × ℕ => CodeStratum ek.1 (ek.2+1)) ∧
  (∀ c, SpatialPerfect c ↔ ∃ κ, 0 < κ ∧ CodeStratum c κ) ∧
  SigmaTwo SpatialPerfect ∧
  (¬ ∃ f : ℕ → ℕ, Computable f ∧ ∀ c, SpatialPerfect c → CodeStratum c (f c)) ∧
  (∀ (G : Game), ValueOne G → ¬ HasPerfect G →
    ∀ S : ℕ → PureStrategy G.scenario,
      Filter.Tendsto (fun n => loss G (normalOfPure (S n))) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n => largestSchmidt (S n).vector) Filter.atTop (nhds 0))

end Sigma2


