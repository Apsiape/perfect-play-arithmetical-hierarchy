import Sigma2.ReductionRows

noncomputable section
set_option maxHeartbeats 300000
set_option pp.proofs false
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
namespace Sigma2.ReductionRows
open Sigma2.Tree Sigma2.Reduction Sigma2.Reduction.Syntax
variable {M : Automaton} (A : NormalRealization (applicationPresentation M))

@[simp] theorem eval_sum (xs : List Expr) :
    (sum xs).eval A.support A.label=(xs.map (Expr.eval A.support A.label)).sum := by
  induction xs with
  | nil => simp [sum, Expr.eval] <;> module
  | cons p xs ih => simpa [sum, Expr.eval] using congrArg (fun T => p.eval A.support A.label+T) ih

@[simp] theorem eval_sum_append (xs ys : List Expr) :
    (sum (xs++ys)).eval A.support A.label =
      (sum xs).eval A.support A.label+(sum ys).eval A.support A.label := by
  simp only [eval_sum, List.map_append, List.sum_append]

theorem symbol_partition : ∑ c : Symbol M, A.label (12+c.val)=A.support := by
  have h := fixed_row A
    (sub (sum ((List.ofFn (fun c : Symbol M => c)).map (fun c => sym c.val))) I) (by simp)
  apply sub_eq_zero.mp
  simpa only [eval_sub, eval_I, eval_sum, List.map_map, List.map_ofFn,
    List.sum_ofFn, Function.comp_def, eval_sym] using h

theorem symbol_orthogonal (c d : Symbol M) (hcd : c≠d) :
    A.label (12+c.val)*A.label (12+d.val)=0 := by
  let S : Symbol M → Op := fun c => A.label (12+c.val)
  have hp (c : Symbol M) : Positive (S c) := by
    have h := ContinuousLinearMap.isPositive_adjoint_comp_self (S c)
    change Positive (star (S c)*S c) at h
    have hc : Projection (S c) := typed_symbol A c
    rwa [hc.1,hc.2] at h
  have h := FiniteSpectral.coarse_action S id c A.support A.support_projection hp
    (symbol_partition A) (by simpa [CoarseCells.coarse] using typed_symbol A c) d
  simpa [CoarseCells.coarse, Ne.symm hcd, S] using h

@[simp] theorem eval_sum_flatMap {α : Type} (xs : List α) (f : α → List Expr) :
    (sum (xs.flatMap f)).eval A.support A.label =
      (xs.map (fun x => (sum (f x)).eval A.support A.label)).sum := by
  induction xs with
  | nil => simp [sum, Expr.eval] <;> module
  | cons x xs ih =>
    simpa only [List.flatMap_cons, eval_sum_append, List.map_cons, List.sum_cons] using
      congrArg (fun T => (sum (f x)).eval A.support A.label+T) ih

@[simp] theorem eval_sum_fin {n : ℕ} (f : Fin n → List Expr) :
    (sum ((List.ofFn (fun i : Fin n => i)).flatMap f)).eval A.support A.label =
      ∑ i, (sum (f i)).eval A.support A.label := by
  rw [eval_sum_flatMap]
  simp only [List.map_ofFn, List.sum_ofFn, Function.comp_def]

@[simp] theorem eval_sum_option (f : Option (Symbol M) → List Expr) :
    (sum ((none::(List.ofFn (fun c : Symbol M => c)).map some).flatMap f)).eval A.support A.label =
      ∑ l, (sum (f l)).eval A.support A.label := by
  rw [eval_sum_flatMap]
  simp only [List.map_cons, List.sum_cons, List.map_map, List.map_ofFn,
    List.sum_ofFn, Fintype.sum_option, Function.comp_def]

@[simp] theorem eval_sum_bool (p : Bool → Prop) [DecidablePred p] (f : Bool → Expr) :
    (sum ([false,true].filterMap (fun b => if p b then some (f b) else none))).eval A.support A.label =
      ∑ b : Bool, if p b then (f b).eval A.support A.label else 0 := by
  by_cases hf : p false <;> by_cases ht : p true <;>
    simp [hf, ht, sum, Expr.eval, Fintype.sum_bool, add_comm] <;> module

@[simp] theorem eval_left (l : Option (Symbol M)) :
    (left (l.map Fin.val)).eval A.support A.label = match l with
      | none => A.label 3
      | some c => A.label 1*A.label (12+c.val)*star (A.label 1)*(A.support-A.label 3) := by
  cases l <;> simp [left,Expr.eval]

@[simp] theorem eval_right (r : Symbol M) :
    (right r.val).eval A.support A.label =
      star (A.label 1)*A.label (12+r.val)*A.label 1*
        (A.support-star (A.label 1)*A.label 3*A.label 1)+
      (if r=1 then star (A.label 1)*A.label 3*A.label 1 else 0) := by
  have hr : r.val=1 ↔ r=1 := by
    rw [Fin.ext_iff]
    simp [Nat.mod_eq_of_lt (show 1<M.extraSymbols+3 by omega)]
  by_cases hr1 : r=1 <;> simp [right, Syntax.lastX, Expr.eval, hr, hr1] <;> module

theorem eval_update_sum (a : Symbol M)
    (F : Option (Symbol M) → Symbol M → Symbol M → Bool → Expr) :
    (sum ((none::(List.ofFn (fun c : Symbol M => c)).map some).flatMap (fun l =>
      (List.ofFn (fun c : Symbol M => c)).flatMap (fun c =>
      (List.ofFn (fun c : Symbol M => c)).flatMap (fun r =>
      [false,true].filterMap (fun ε => if M.update l c r ε=a then some (F l c r ε) else none)))))).eval A.support A.label =
      ∑ l, ∑ c, ∑ r, ∑ ε : Bool,
        if M.update l c r ε=a then (F l c r ε).eval A.support A.label else 0 := by
  rw [eval_sum_option]
  apply Finset.sum_congr rfl
  intro l _
  rw [eval_sum_fin]
  apply Finset.sum_congr rfl
  intro c _
  rw [eval_sum_fin]
  apply Finset.sum_congr rfl
  intro r _
  exact eval_sum_bool A _ _

attribute [local irreducible] Sigma2.Reduction.Syntax.sum List.ofFn

set_option maxHeartbeats 300000 in
theorem transition_row (a : Symbol M) :
    let C := coordinates A
    let lastX := star C.ux*C.px*C.ux
    let lastY := star C.uy*C.py*C.uy
    let L : Option (Symbol M) → Op := fun l => match l with
      | none => C.px
      | some c => C.ux*A.label (12+c.val)*star C.ux*(A.support-C.px)
    let N : Symbol M → Op := fun r => star C.ux*A.label (12+r.val)*C.ux*(A.support-lastX)+
      (if r=1 then lastX else 0)
    (star C.uy*A.label (12+a.val)*C.uy-
      ∑ l, ∑ c, ∑ r, ∑ ε : Bool,
        if M.update l c r ε=a then L l*A.label (12+c.val)*N r*(if ε then A.label 10 else A.support-A.label 10) else 0)*
      (A.support-lastY)=0 := by
  have h := A.central_equations (transition M a)
    (List.mem_append_right _ (List.mem_map.mpr ⟨a,List.mem_ofFn.mpr ⟨a,rfl⟩,rfl⟩))
  dsimp only [Syntax.transition] at h
  rw [Expr.eval, eval_sub, eval_sub, eval_update_sum] at h
  simpa only [eval_sub, eval_mul3, Expr.eval, eval_L, eval_I,
    Syntax.lastX, Syntax.lastY, eval_sym, eval_update_sum, apply_ite,
    eval_left, eval_right, coordinates] using h

def tableau : Tableau A (coordinates A) M where
  symbol := fun c => A.label (12+c.val)
  pulse := A.label 10
  projections := typed_symbol A
  orthogonal := symbol_orthogonal A
  partition := symbol_partition A
  pulse_projection := typed_10 A
  centralizer := ⟨fun c => A.centralizer _,A.centralizer _⟩
  supported := ⟨fun c => A.label_supported _,A.label_supported _⟩
  initial_start := by
    apply sub_eq_zero.mp
    simpa [coordinates,Expr.eval] using fixed_row A
      (sub (mul3 (sym 0) (L 3) (L 4)) (.mul (L 3) (L 4))) (by simp)
  initial_blank := by
    apply sub_eq_zero.mp
    simpa [coordinates,Expr.eval] using fixed_row A
      (sub (mul3 (sym 1) (sub I (L 3)) (L 4)) (.mul (sub I (L 3)) (L 4))) (by simp)
  no_halt := by
    change A.label (12+(2 % (M.extraSymbols+3)))=0
    rw [Nat.mod_eq_of_lt (show 2<M.extraSymbols+3 by omega)]
    exact fixed_row A (sym 2) (by simp)
  transition := transition_row A

#print axioms symbol_partition
#print axioms symbol_orthogonal
#print axioms tableau
end Sigma2.ReductionRows
