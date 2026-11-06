import Sigma2.SimulatorLocal
import Sigma2.SimulatorFinite

noncomputable section
set_option maxHeartbeats 400000
namespace Sigma2.SimulatorFold
open Turing Sigma2.SimulatorLocal

variable {A : Type}

/-- Position x stores the nonnegative cell x and the negative cell -x-1. -/
def fold (v : ℤ → A) (x : ℕ) : A × A := (v x, v (-(x : ℤ)-1))

/-- At the boundary, the two halves become each other's missing neighbor. -/
def halfRule (F : A → A → A → A) (l : Option (A × A)) (c r : A × A) : A × A :=
  (F ((l.map Prod.fst).getD c.2) c.1 r.1,
    F r.2 c.2 ((l.map Prod.snd).getD c.1))

def halfStep (F : A → A → A → A) (v : ℕ → A × A) (x : ℕ) : A × A :=
  halfRule F (if x=0 then none else some (v (x-1))) (v x) (v (x+1))

/-- Folding preserves every radius-one step, with no slowdown and no wall
assumption on the two-way tape. -/
theorem halfStep_fold (F : A → A → A → A) (v : ℤ → A) :
    halfStep F (fold v) = fold (fun z => F (v (z-1)) (v z) (v (z+1))) := by
  funext x
  cases x with
  | zero => simp [halfStep, halfRule, fold]
  | succ n =>
    apply Prod.ext <;>
      simp [halfStep, halfRule, fold, Nat.succ_ne_zero] <;>
      congr 1 <;> congr 1 <;> omega

theorem fold_injective : Function.Injective (fold : (ℤ → A) → ℕ → A × A) := by
  intro v w h
  funext z
  cases z with
  | ofNat n => exact congrArg (fun u => (u n).1) h
  | negSucc n =>
    have hh := congrArg (fun u => (u n).2) h
    simpa [fold, Int.negSucc_eq, sub_eq_add_neg, add_comm] using hh

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]

/-- One exact Mathlib TM0 step on a radius-one half-line rule. -/
theorem halfStep_picture (M : TM0.Machine Γ Q) (c : Positioned Γ Q) :
    halfStep (localRule M) (fold (picture c)) = fold (picture (advance M c)) := by
  rw [halfStep_fold]
  exact congrArg fold (lineStep_picture M c)

/-- All-time head/tape simulation, including arbitrary leftward excursions. -/
theorem halfRun_picture (M : TM0.Machine Γ Q) (c : Positioned Γ Q) (t : ℕ) :
    (halfStep (localRule M))^[t] (fold (picture c)) =
      fold (picture ((advance M)^[t] c)) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, halfStep_picture]

/-- Compose extraction, finite restriction, and the CA simulation. The input
picture is already loaded; constructing it from the pulse remains separate. -/
theorem predicate_halfline (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Inhabited Q)
      (M : TM0.Machine SimulatorMachine.TapeAlphabet Q),
      ∀ v : List.Vector ℕ 3, ∃ (t : ℕ) (c : Positioned SimulatorMachine.TapeAlphabet Q),
        (halfStep (localRule M))^[t]
          (fold (picture (0, TM0.init (SimulatorMachine.input v.val)))) = fold (picture c) ∧
        TM0.step M c.2 = none ∧
        SimulatorMachine.OutputEncodes c.2.Tape.right₀ [SimulatorMachine.result R v] := by
  obtain ⟨Q, hQ, iQ, M, hM⟩ := SimulatorFinite.predicate_finite_machine R hR
  letI := hQ
  letI := iQ
  refine ⟨Q, hQ, iQ, M, ?_⟩
  intro v
  obtain ⟨w, hw, ho⟩ := hM v
  obtain ⟨t, hh, he⟩ := eventual_output M (SimulatorMachine.input v.val) w hw
  refine ⟨t, (advance M)^[t] (0, TM0.init (SimulatorMachine.input v.val)),
    halfRun_picture M _ t, hh, ?_⟩
  rw [he]
  exact ho

#print axioms halfStep_fold
#print axioms fold_injective
#print axioms halfStep_picture
#print axioms halfRun_picture
#print axioms predicate_halfline
end Sigma2.SimulatorFold

