import Sigma2.ReductionPresentation

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 300000
set_option pp.proofs false
namespace Sigma2.ReductionEval
open Sigma2.Tree Sigma2.Reduction Sigma2.Reduction.Syntax
variable {M : Automaton} (label : ℕ → Op)

@[simp] theorem eval_I : I.eval 1 label=1 := by simp [I,Expr.eval]
@[simp] theorem eval_L (i : ℕ) : (L i).eval 1 label=label i := rfl
@[simp] theorem eval_sub (p q : Expr) :
    (sub p q).eval 1 label=p.eval 1 label-q.eval 1 label := by
  simp [sub,neg,Expr.eval,smul_mul_assoc,sub_eq_add_neg]
  module
@[simp] theorem eval_mul3 (p q r : Expr) :
    (mul3 p q r).eval 1 label=p.eval 1 label*q.eval 1 label*r.eval 1 label := rfl
@[simp] theorem eval_sym (c : ℕ) : (sym c).eval 1 label=label (12+c) := rfl

@[simp] theorem eval_sum (xs : List Expr) :
    (sum xs).eval (1:Op) label=(xs.map (Expr.eval (1:Op) label)).sum := by
  induction xs with
  | nil => simp [sum, Expr.eval] <;> module
  | cons p xs ih => simpa [sum, Expr.eval] using congrArg (fun T => p.eval (1:Op) label+T) ih

@[simp] theorem eval_sum_append (xs ys : List Expr) :
    (sum (xs++ys)).eval (1:Op) label =
      (sum xs).eval (1:Op) label+(sum ys).eval (1:Op) label := by
  simp only [eval_sum, List.map_append, List.sum_append]

@[simp] theorem eval_sum_flatMap {α : Type} (xs : List α) (f : α → List Expr) :
    (sum (xs.flatMap f)).eval (1:Op) label =
      (xs.map (fun x => (sum (f x)).eval (1:Op) label)).sum := by
  induction xs with
  | nil => simp [sum, Expr.eval] <;> module
  | cons x xs ih =>
    simpa only [List.flatMap_cons, eval_sum_append, List.map_cons, List.sum_cons] using
      congrArg (fun T => (sum (f x)).eval (1:Op) label+T) ih

@[simp] theorem eval_sum_fin {n : ℕ} (f : Fin n → List Expr) :
    (sum ((List.ofFn (fun i : Fin n => i)).flatMap f)).eval (1:Op) label =
      ∑ i, (sum (f i)).eval (1:Op) label := by
  rw [eval_sum_flatMap]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]

@[simp] theorem eval_sum_option (f : Option (Symbol M) → List Expr) :
    (sum ((none::(List.ofFn (fun c : Symbol M => c)).map some).flatMap f)).eval (1:Op) label =
      ∑ l, (sum (f l)).eval (1:Op) label := by
  rw [eval_sum_flatMap]
  simp only [List.map_cons, List.sum_cons, List.map_map, List.map_ofFn,
    List.sum_ofFn, Fintype.sum_option, Function.comp_def]

@[simp] theorem eval_sum_bool (p : Bool → Prop) [DecidablePred p] (f : Bool → Expr) :
    (sum ([false,true].filterMap (fun b => if p b then some (f b) else none))).eval (1:Op) label =
      ∑ b : Bool, if p b then (f b).eval (1:Op) label else 0 := by
  by_cases hf : p false <;> by_cases ht : p true <;>
    simp [hf, ht, sum, Expr.eval, Fintype.sum_bool, add_comm] <;> module

@[simp] theorem eval_left (l : Option (Symbol M)) :
    (left (l.map Fin.val)).eval (1:Op) label = match l with
      | none => label 3
      | some c => label 1*label (12+c.val)*star (label 1)*((1:Op)-label 3) := by
  cases l <;> simp [left,Expr.eval]

@[simp] theorem eval_right (r : Symbol M) :
    (right r.val).eval (1:Op) label =
      star (label 1)*label (12+r.val)*label 1*
        ((1:Op)-star (label 1)*label 3*label 1)+
      (if r=1 then star (label 1)*label 3*label 1 else 0) := by
  have hr : r.val=1 ↔ r=1 := by
    rw [Fin.ext_iff]
    simp [Nat.mod_eq_of_lt (show 1<M.extraSymbols+3 by omega)]
  by_cases hr1 : r=1 <;> simp [right, Syntax.lastX, Expr.eval, hr, hr1] <;> module

theorem eval_update_sum (a : Symbol M)
    (F : Option (Symbol M) → Symbol M → Symbol M → Bool → Expr) :
    (sum ((none::(List.ofFn (fun c : Symbol M => c)).map some).flatMap (fun l =>
      (List.ofFn (fun c : Symbol M => c)).flatMap (fun c =>
      (List.ofFn (fun c : Symbol M => c)).flatMap (fun r =>
      [false,true].filterMap (fun ε => if M.update l c r ε=a then some (F l c r ε) else none)))))).eval (1:Op) label =
      ∑ l, ∑ c, ∑ r, ∑ ε : Bool,
        if M.update l c r ε=a then (F l c r ε).eval (1:Op) label else 0 := by
  rw [eval_sum_option]
  apply Finset.sum_congr rfl
  intro l _
  rw [eval_sum_fin]
  apply Finset.sum_congr rfl
  intro c _
  rw [eval_sum_fin]
  apply Finset.sum_congr rfl
  intro r _
  exact eval_sum_bool label _ _

attribute [local irreducible] Sigma2.Reduction.Syntax.sum List.ofFn

theorem eval_transition (a : Symbol M) :
    (transition M a).eval 1 label=
    (star (label 2)*label (12+a.val)*label 2-
      ∑ l : Option (Symbol M), ∑ c : Symbol M, ∑ r : Symbol M, ∑ ε : Bool,
        if M.update l c r ε=a then
          (match l with
            | none => label 3
            | some c => label 1*label (12+c.val)*star (label 1)*(1-label 3))*
          label (12+c.val)*
          (star (label 1)*label (12+r.val)*label 1*(1-star (label 1)*label 3*label 1)+
            (if r=1 then star (label 1)*label 3*label 1 else 0))*
          (if ε then label 10 else 1-label 10) else 0)*
      (1-star (label 2)*label 4*label 2) := by
  dsimp only [Syntax.transition]
  rw [Expr.eval,eval_sub,eval_sub,eval_update_sum]
  simp only [eval_sub,eval_mul3,Expr.eval,eval_L,eval_I,
    Syntax.lastX,Syntax.lastY,eval_sym,apply_ite,eval_left,eval_right]

#print axioms eval_transition
end Sigma2.ReductionEval
