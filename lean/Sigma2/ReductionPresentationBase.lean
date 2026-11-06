import Sigma2.ReductionInterface
import Sigma2.SimulatorUniform
import Sigma2.SimulatorEffective

noncomputable section
open scoped BigOperators
namespace Sigma2.Reduction
open Sigma2.Tree

/-- Section 7: effective half-line radius-one simulation with unary front,
frozen input, prime-rank decoding, and the sequential checks. -/
theorem effective_program (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ e, ProgramCorrect R e (decodeAutomaton (f e)) := by
  exact SimulatorEffective.effective_program R hR

def programCode (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) : ℕ → ℕ :=
  Classical.choose (effective_program R hR)

theorem programCode_computable (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    Computable (programCode R hR) := (Classical.choose_spec (effective_program R hR)).1

/- Explicit rational star-polynomial construction, with exactly the label table
of Section 4: root, Ux,Uy,Px,Py,W,C,Z,J,K,return,inverse, then tableau symbols. -/
namespace Syntax
open Expr

def I : Expr := .scalar 1
def L (i : ℕ) : Expr := .label i
def neg (a : Expr) : Expr := .mul (.scalar (-1)) a
def sub (a b : Expr) : Expr := .add a (neg b)
def sum (xs : List Expr) : Expr := xs.foldr Expr.add (.scalar 0)
def comm (a b : Expr) : Expr := sub (.mul a b) (.mul b a)
def mul3 (a b c : Expr) : Expr := .mul (.mul a b) c
def lastX : Expr := mul3 (.adj (L 1)) (L 3) (L 1)
def lastY : Expr := mul3 (.adj (L 2)) (L 4) (L 2)
def sym (c : ℕ) : Expr := L (12+c)

def left (l : Option ℕ) : Expr := match l with
  | none => L 3
  | some c => .mul (mul3 (L 1) (sym c) (.adj (L 1))) (sub I (L 3))
def right (r : ℕ) : Expr := .add
  (.mul (mul3 (.adj (L 1)) (sym r) (L 1)) (sub I lastX))
  (if r=1 then lastX else .scalar 0)

def transition (M : Automaton) (a : Symbol M) : Expr :=
  let syms : List (Symbol M) := List.ofFn (fun c : Symbol M => c)
  let terms := (none::syms.map some).flatMap (fun l => syms.flatMap (fun c =>
    syms.flatMap (fun r => [false,true].filterMap (fun ε =>
      if M.update l c r ε=a then some (.mul (mul3 (left (l.map Fin.val)) (sym c.val) (right r.val))
        (if ε then L 10 else sub I (L 10))) else none))))
  .mul (sub (mul3 (.adj (L 2)) (sym a.val) (L 2)) (sum terms)) (sub I lastY)

end Syntax

open Syntax in
def buildPresentation (M : Automaton) : Presentation where
  types := [.projection,.unitary,.unitary,.projection,.projection,.unitary,.positive,
    .unitary,.unitary,.unitary,.projection,.contraction] ++ List.replicate (M.extraSymbols+3) .projection
  root := 0
  transported := List.range 10
  central := []
  endpoints := []
  zeros := []
  linear := []

/- All application rows are constructed explicitly; the separate definition
avoids hiding a table-generation proof in an opaque operator predicate. -/
open Syntax in
def applicationPresentation (M : Automaton) : Presentation :=
  let syms : List (Symbol M) := List.ofFn (fun c : Symbol M => c)
  let endpointCoords : List (Expr × Fin 4 × Fin 4 × Expr) :=
    (List.ofFn (fun b : Fin 2 => b)).flatMap (fun b =>
      [(L 1,⟨b.val,by omega⟩,⟨b.val+2,by omega⟩,I),
       (L 1,⟨b.val+2,by omega⟩,⟨b.val,by omega⟩,L 1),
       (L 3,⟨b.val,by omega⟩,⟨b.val,by omega⟩,L 3)]) ++
    (List.ofFn (fun a : Fin 2 => a)).flatMap (fun a =>
      [(L 2,⟨2*a.val,by omega⟩,⟨2*a.val+1,by omega⟩,I),
       (L 2,⟨2*a.val+1,by omega⟩,⟨2*a.val,by omega⟩,L 2),
       (L 4,⟨2*a.val,by omega⟩,⟨2*a.val,by omega⟩,L 4)])
  let endpointClock : List (Expr × Fin 4 × Fin 4 × Expr) :=
    (List.ofFn (fun a : Fin 4 => a)).flatMap (fun a =>
      [(L 5,a,a,.mul (if a.val%2=0 then I else L 7) (.mul (L 5) (L 5))),
       (L 6,a,a,.mul (.scalar (if a.val%2=0 then 1 else 1/2)) (.mul (L 6) (L 6))),
       (L 7,a,a,L 7),(L 8,a,a,L 8),(L 9,a,a,L 9)])
  { (buildPresentation M) with
    central :=
      [sub (.mul (L 1) (L 0)) (L 0),sub (.mul (L 2) (L 0)) (L 0),
       sub (.mul (L 3) (L 0)) (L 0),sub (.mul (L 4) (L 0)) (L 0),
       sub (.mul (L 5) (L 0)) (L 0),sub (.mul (L 6) (L 0)) (L 0),
       sub (.mul (L 8) (L 9)) (mul3 (L 7) (L 9) (L 8)),
       .mul (sub (L 5) I) (L 10),
       sub (.mul (L 11) (sub (L 5) I)) (.mul (.scalar (1/2)) (.mul (L 6) (sub I (L 10)))),
       sub (mul3 (sym 0) (L 3) (L 4)) (.mul (L 3) (L 4)),
       sub (mul3 (sym 1) (sub I (L 3)) (L 4)) (.mul (sub I (L 3)) (L 4)),
       sym 2,sub (sum (syms.map (fun c => sym c.val))) I] ++
      ([0,1,2,3,4,5,6,8,9,10,11] ++ syms.map (fun (c : Symbol M) => 12+c.val)).map (fun i => comm (L 7) (L i)) ++
      syms.map (transition M)
    endpoints := endpointCoords ++ endpointClock
    zeros := (List.ofFn (fun b : Fin 2 => (L 3,(⟨b.val+2,by omega⟩ : Fin 4)))) ++
      (List.ofFn (fun a : Fin 2 => (L 4,(⟨2*a.val+1,by omega⟩ : Fin 4)))) }

namespace Admissibility
open Syntax

def LabelBound (n : ℕ) : Expr → Prop
  | .scalar _ => True
  | .label i => i < n
  | .add p q | .mul p q => LabelBound n p ∧ LabelBound n q
  | .adj p => LabelBound n p

theorem labels_lt {n : ℕ} {p : Expr} (hp : LabelBound n p) :
    ∀ i ∈ p.labels, i < n := by
  induction p with
  | scalar q => simp [Expr.labels]
  | label k => simpa [Expr.labels, LabelBound] using hp
  | add p q ihp ihq | mul p q ihp ihq =>
    intro i hi
    simp only [Expr.labels, List.mem_append] at hi
    rcases hi with hi | hi
    · exact ihp hp.1 i hi
    · exact ihq hp.2 i hi
  | adj p ih => exact ih hp

theorem sum_bound (n : ℕ) (xs : List Expr)
    (h : ∀ p ∈ xs, LabelBound n p) : LabelBound n (Syntax.sum xs) := by
  induction xs with
  | nil => trivial
  | cons p xs ih =>
    change LabelBound n p ∧ LabelBound n (Syntax.sum xs)
    exact ⟨h p (by simp), ih (fun q hq => h q (by simp [hq]))⟩

theorem transition_bound (M : Tree.Automaton) (a : Tree.Symbol M) :
    LabelBound (M.extraSymbols + 15) (transition M a) := by
  let n := M.extraSymbols + 15
  have hs (c : Tree.Symbol M) : LabelBound n (sym c.val) := by
    have hc := c.isLt
    simp only [sym, L, LabelBound]
    dsimp [n]
    omega
  have hl (l : Option (Tree.Symbol M)) : LabelBound n (left (l.map Fin.val)) := by
    cases l with
    | none => simp [left, L, LabelBound, n] <;> omega
    | some c =>
      have hc := c.isLt
      simp [left, mul3, sym, sub, neg, I, L, LabelBound, n] <;> omega
  have hr (c : Tree.Symbol M) : LabelBound n (right c.val) := by
    have hc := c.isLt
    by_cases hc1 : c.val = 1 <;>
      simp [right, Syntax.lastX, hc1, mul3, sym, sub, neg, I, L, LabelBound, n] <;> omega
  have he (ε : Bool) : LabelBound n (if ε then L 10 else sub I (L 10)) := by
    cases ε <;> simp [sub, neg, I, L, LabelBound, n] <;> omega
  have ht : ∀ p ∈
      ((none :: (List.ofFn (fun c : Tree.Symbol M => c)).map some).flatMap (fun l =>
      (List.ofFn (fun c : Tree.Symbol M => c)).flatMap (fun c =>
      (List.ofFn (fun c : Tree.Symbol M => c)).flatMap (fun r =>
      [false,true].filterMap (fun ε => if M.update l c r ε=a then
        some (.mul (mul3 (left (l.map Fin.val)) (sym c.val) (right r.val))
          (if ε then L 10 else sub I (L 10))) else none))))), LabelBound n p := by
    intro p hp
    rcases List.mem_flatMap.mp hp with ⟨l, _, hp⟩
    rcases List.mem_flatMap.mp hp with ⟨c, _, hp⟩
    rcases List.mem_flatMap.mp hp with ⟨r, _, hp⟩
    rcases List.mem_filterMap.mp hp with ⟨ε, _, hp⟩
    by_cases hu : M.update l c r ε=a
    · rw [if_pos hu] at hp
      have hp' := Option.some.inj hp
      subst p
      exact ⟨⟨⟨hl l, hs c⟩, hr r⟩, he ε⟩
    · simp [hu] at hp
  change LabelBound n (transition M a)
  dsimp only [transition]
  have hb : LabelBound n (mul3 (.adj (L 2)) (sym a.val) (L 2)) := by
    change (2 < n ∧ LabelBound n (sym a.val)) ∧ 2 < n
    exact ⟨⟨by dsimp [n]; omega, hs a⟩, by dsimp [n]; omega⟩
  have hy : LabelBound n (sub I Syntax.lastY) := by
    simp [Syntax.lastY, mul3, sub, neg, I, L, LabelBound, n] <;> omega
  simpa only [sub, neg, I, LabelBound, true_and] using
    And.intro (And.intro hb (sum_bound n _ ht)) hy

end Admissibility

open Admissibility Syntax

/-- Section 7, admissibility is a finite syntactic property of the actual rows. -/
theorem application_admissible (M : Automaton) : (applicationPresentation M).admissible := by
  let n := M.extraSymbols + 15
  have hlen : (applicationPresentation M).types.length = n := by
    simp [applicationPresentation, buildPresentation, n] <;> omega
  have hsum : LabelBound n (Syntax.sum
      ((List.ofFn (fun c : Tree.Symbol M => c)).map (fun c => sym c.val))) := by
    apply sum_bound
    intro p hp
    rcases List.mem_map.mp hp with ⟨c, _, rfl⟩
    have hc := c.isLt
    simp only [sym, L, LabelBound]
    dsimp [n]
    omega
  have hcentral : ∀ p ∈ (applicationPresentation M).central, LabelBound n p := by
    intro p hp
    dsimp only [applicationPresentation] at hp
    simp only [List.mem_append] at hp
    rcases hp with (hf | hm) | ht
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      all_goals try exact ⟨hsum, trivial, trivial⟩
      all_goals simp [sub, neg, mul3, sym, I, L, LabelBound, n] <;> omega
    · rcases List.mem_map.mp hm with ⟨i, hi, rfl⟩
      have hib : i < n := by
        simp only [List.mem_append] at hi
        rcases hi with hi | hi
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals dsimp [n]; omega
        · rcases List.mem_map.mp hi with ⟨c, _, rfl⟩
          have hc := c.isLt
          dsimp [n]
          omega
      simp [Syntax.comm, sub, neg, I, L, LabelBound, hib, n] <;> omega
    · rcases List.mem_map.mp ht with ⟨c, _, rfl⟩
      exact transition_bound M c
  unfold Presentation.admissible
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [applicationPresentation, buildPresentation]
  · intro i hi
    rw [hlen]
    change i ∈ List.range 10 at hi
    have hi' := List.mem_range.mp hi
    dsimp [n]
    omega
  · intro p hp i hi
    rw [hlen]
    exact labels_lt (hcentral p hp) i hi
  · intro r hr
    dsimp only [applicationPresentation] at hr
    simp only [List.mem_append, List.mem_flatMap] at hr
    rcases hr with (⟨b, _, hr⟩ | ⟨a, _, hr⟩) | ⟨a, _, hr⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      all_goals
        constructor
        · simp [applicationPresentation, buildPresentation, Expr.labels, L, List.mem_range]
        · rw [hlen]
          apply labels_lt
          simp [I, L, LabelBound, n] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      all_goals
        constructor
        · simp [applicationPresentation, buildPresentation, Expr.labels, L, List.mem_range]
        · rw [hlen]
          apply labels_lt
          simp [I, L, LabelBound, n] <;> omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      all_goals
        constructor
        · simp [applicationPresentation, buildPresentation, Expr.labels, L, List.mem_range]
        · rw [hlen]
          apply labels_lt
          try split_ifs
          all_goals simp [sub, neg, I, L, LabelBound, n] <;> omega
  · intro r hr
    dsimp only [applicationPresentation] at hr
    simp only [List.mem_append, List.mem_ofFn] at hr
    rcases hr with ⟨b, rfl⟩ | ⟨a, rfl⟩ <;>
      simp [applicationPresentation, buildPresentation, Expr.labels, L, List.mem_range]
  · simp [applicationPresentation, buildPresentation]

def inputPresentation (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) : Presentation :=
  applicationPresentation (decodeAutomaton (programCode R hR e))

end Sigma2.Reduction
