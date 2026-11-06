import Sigma2.SimulatorFold
import Sigma2.SimulatorAlphabet

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Sigma2.SimulatorTracks
open Turing Sigma2.Tree Sigma2.SimulatorLocal Sigma2.SimulatorFold

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]

abbrev State (Γ Q : Type) := Fin 5 × (Cell Γ Q × Cell Γ Q)

def vacant : Cell Γ Q := (default, none)
def start : State Γ Q := (0, ((default, some default), vacant))
def blank : State Γ Q := (1, (vacant, vacant))
def reject : State Γ Q := (2, (vacant, vacant))

def update (M : TM0.Machine Γ Q) (l : Option (State Γ Q)) (c r : State Γ Q)
    (b : Bool) : State Γ Q :=
  (SimulatorFront.front.update (l.map Prod.fst) c.1 r.1 b,
    halfRule (localRule M) (l.map Prod.snd) c.2 r.2)

/-- The computation track and the frozen pulse track share one radius-one rule. -/
def rule (M : TM0.Machine Γ Q) : SimulatorAlphabet.Rule (State Γ Q) where
  start := start
  blank := blank
  reject := reject
  start_ne_blank := by intro h; have := congrArg Prod.fst h; simpa [start, blank] using this
  start_ne_reject := by intro h; have := congrArg Prod.fst h; simpa [start, reject] using this
  blank_ne_reject := by intro h; have := congrArg Prod.fst h; simpa [blank, reject] using this
  update := update M
  quiescence := by
    intro b
    simp [update, blank, vacant, halfRule, localRule, written, stationary, incoming]

/-- Every pulse front is retained exactly, independently of the machine run. -/
theorem front_run (M : TM0.Machine Γ Q) (pulse : ℕ → Bool) (t x : ℕ) :
    (SimulatorAlphabet.typedRun (rule M) pulse t x).1 =
      run SimulatorFront.front pulse t x := by
  induction t generalizing x with
  | zero => by_cases hx : x=0 <;> simp [SimulatorAlphabet.typedRun, rule, start, blank, run, hx]
  | succ t ih =>
    change (update M (if x=0 then none else some (SimulatorAlphabet.typedRun (rule M) pulse t (x-1)))
      (SimulatorAlphabet.typedRun (rule M) pulse t x)
      (SimulatorAlphabet.typedRun (rule M) pulse t (x+1)) (pulse t)).1 = _
    by_cases hx : x=0 <;> simp [update, run, hx, ih]

lemma empty_tape (z : ℤ) : (Tape.mk₁ ([] : List Γ)).nth z = default := by
  cases z with
  | ofNat n => cases n <;> simp [Tape.nth, Tape.mk₁, Tape.mk₂, Tape.mk']
  | negSucc n => simp [Tape.nth, Tape.mk₁, Tape.mk₂, Tape.mk']

lemma initial_picture (x : ℕ) :
    fold (picture (0, (TM0.init [] : TM0.Cfg Γ Q))) x =
      if x=0 then ((default, some default), vacant) else (vacant, vacant) := by
  have hn : -(x : ℤ)-1 ≠ 0 := by omega
  dsimp only [fold, picture, TM0.init]
  simp only [empty_tape]
  by_cases hx : x=0 <;> simp [hx, hn, vacant]

def snapshot (M : TM0.Machine Γ Q) (pulse : ℕ → Bool) (c : Positioned Γ Q)
    (t x : ℕ) : State Γ Q :=
  (run SimulatorFront.front pulse t x, fold (picture ((advance M)^[t] c)) x)

/-- A joint pulse/computation snapshot evolves exactly in one local step. -/
theorem snapshot_step (M : TM0.Machine Γ Q) (pulse : ℕ → Bool) (c : Positioned Γ Q)
    (t x : ℕ) :
    update M (if x=0 then none else some (snapshot M pulse c t (x-1)))
      (snapshot M pulse c t x) (snapshot M pulse c t (x+1)) (pulse t) =
        snapshot M pulse c (t+1) x := by
  have hc := congrFun (halfStep_picture M ((advance M)^[t] c)) x
  apply Prod.ext
  · by_cases hx : x=0 <;> simp [update, snapshot, run, hx]
  · by_cases hx : x=0 <;>
      simpa [update, snapshot, halfStep, hx, Function.iterate_succ_apply'] using hc

/-- On the prescribed initial start/blank configuration, the actual typed CA
runs the machine on an empty tape while recording the pulse forever. -/
theorem typed_run_snapshot (M : TM0.Machine Γ Q) (pulse : ℕ → Bool) (t x : ℕ) :
    SimulatorAlphabet.typedRun (rule M) pulse t x =
      snapshot M pulse (0, TM0.init []) t x := by
  induction t generalizing x with
  | zero =>
    by_cases hx : x=0 <;>
      simp [SimulatorAlphabet.typedRun, rule, snapshot, run, start, blank, initial_picture, hx]
  | succ t ih =>
    change update M (if x=0 then none else some (SimulatorAlphabet.typedRun (rule M) pulse t (x-1)))
      (SimulatorAlphabet.typedRun (rule M) pulse t x)
      (SimulatorAlphabet.typedRun (rule M) pulse t (x+1)) (pulse t) = _
    simp only [ih]
    exact snapshot_step M pulse (0, TM0.init []) t x

variable [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]

/-- The machine and front expressed in the original finite-symbol CA type. -/
def automaton (M : TM0.Machine Γ Q) : Automaton := SimulatorAlphabet.automaton (rule M)

/-- Kernel-checked execution in the unchanged Tree.run interface. -/
theorem run_snapshot (M : TM0.Machine Γ Q) (pulse : ℕ → Bool) (t x : ℕ) :
    SimulatorAlphabet.decode (rule M) (run (automaton M) pulse t x) =
      snapshot M pulse (0, TM0.init []) t x := by
  exact (SimulatorAlphabet.decode_run (rule M) pulse t x).trans
    (typed_run_snapshot M pulse t x)

/-- Frozen unary input survives the simultaneous computation track. -/
theorem frozen_period (M : TM0.Machine Γ Q) (q : ℕ) (hq : 0<q)
    (t : ℕ) (ht : q+1≤t) :
    (SimulatorAlphabet.decode (rule M) (run (automaton M) (fun s => decide (q ∣ s)) t 1)).1=4 ∧
    (∀ x, 1<x → x≤q →
      (SimulatorAlphabet.decode (rule M) (run (automaton M) (fun s => decide (q ∣ s)) t x)).1=3) ∧
    (SimulatorAlphabet.decode (rule M) (run (automaton M) (fun s => decide (q ∣ s)) t (q+1))).1=4 := by
  simpa only [run_snapshot, snapshot] using SimulatorFront.front_period_input q hq t ht

/-- An explicitly loaded tape executes in the same finite-symbol automaton.
This theorem does not construct the loader from the prescribed start state. -/
theorem loaded_run_snapshot (M : TM0.Machine Γ Q) (pulse : ℕ → Bool)
    (c : Positioned Γ Q) (t x : ℕ) :
    SimulatorAlphabet.decode (rule M)
      (SimulatorAlphabet.runFrom (automaton M) pulse
        (fun y => SimulatorAlphabet.encode (rule M) (snapshot M pulse c 0 y)) t x) =
      snapshot M pulse c t x := by
  induction t generalizing x with
  | zero => exact SimulatorAlphabet.decode_encode (rule M) _
  | succ t ih =>
    change SimulatorAlphabet.decode (rule M)
      ((SimulatorAlphabet.automaton (rule M)).update _ _ _ _) = _
    rw [SimulatorAlphabet.decode_update]
    change update M _ _ _ _ = _
    by_cases hx : x=0 <;>
      simpa [hx, ih] using snapshot_step M pulse c t x

/-- Exact halting output through the actual finite-symbol CA on prepared input. -/
theorem loaded_output (M : TM0.Machine Γ Q) (pulse : ℕ → Bool)
    (v : List Γ) (w : ListBlank Γ) (hw : w ∈ TM0.eval M v) :
    ∃ (t : ℕ) (c : Positioned Γ Q), TM0.step M c.2 = none ∧ c.2.Tape.right₀ = w ∧
      ∀ x, (SimulatorAlphabet.decode (rule M)
        (SimulatorAlphabet.runFrom (automaton M) pulse
          (fun y => SimulatorAlphabet.encode (rule M)
            (snapshot M pulse (0, TM0.init v) 0 y)) t x)).2 = fold (picture c) x := by
  obtain ⟨t, hh, he⟩ := eventual_output M v w hw
  refine ⟨t, (advance M)^[t] (0, TM0.init v), hh, he, ?_⟩
  intro x
  rw [loaded_run_snapshot]
  rfl

#print axioms front_run
#print axioms snapshot_step
#print axioms typed_run_snapshot
#print axioms run_snapshot
#print axioms frozen_period
#print axioms loaded_run_snapshot
#print axioms loaded_output
end Sigma2.SimulatorTracks

