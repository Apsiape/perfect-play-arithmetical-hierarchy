import Sigma2.TableauGeometry

noncomputable section
namespace Sigma2.SimulatorFront
open Sigma2.Tree

/-- Immutable pulse cells: start, blank, and halt retain the paper's codes;
3 and 4 record false and true. -/
def pulseSymbol (b : Bool) : Fin 5 := if b then 4 else 3

abbrev front : Automaton where
  extraSymbols := 2
  update := fun l c _ b =>
    if c=1 ∧ l≠some 1 ∧ l≠none then pulseSymbol b else c
  blank_quiescence := by intro b; simp

lemma front_update (l : Option (Fin 5)) (c d : Fin 5) (b : Bool) :
    front.update l c d b = if c=1 ∧ l≠some 1 ∧ l≠none then pulseSymbol b else c := rfl

/-- At time t the first t nonboundary cells store the pulse prefix forever. -/
theorem front_run (pulse : ℕ → Bool) (t x : ℕ) :
    run front pulse t x = if x=0 then 0 else
      if x≤t then pulseSymbol (pulse (x-1)) else 1 := by
  induction t generalizing x with
  | zero => by_cases hx : x=0 <;> simp [run, hx]
  | succ t ih =>
    by_cases hx : x=0
    · subst x
      simp only [run, ih]; simp
    by_cases hxt : x≤t
    · have hsym : pulseSymbol (pulse (x-1)) ≠ (1 : Fin 5) := by
        unfold pulseSymbol; split <;> decide
      simp only [run, ih]; simp [hx, hxt, show x≤t+1 by omega, hsym]
    by_cases hnext : x=t+1
    · subst x
      by_cases ht : t=0
      · subst t
        simp only [run]; simp [pulseSymbol]
      · have hsym : pulseSymbol (pulse (t-1)) ≠ (1 : Fin 5) := by
          unfold pulseSymbol; split <;> decide
        simp only [run, ih]
        simp [show ¬ t+1≤t by omega, ht, hsym]
    · have hblank : run front pulse (t+1) x=1 := run_blank front pulse _ _ (by omega)
      simpa only [ite_eq_right hx, ite_eq_right (show ¬x≤t+1 by omega)] using hblank

/-- Once written, a pulse cell is frozen; later pulses cannot overwrite it. -/
theorem front_frozen (pulse : ℕ → Bool) (x t s : ℕ)
    (hx : 0<x) (ht : x≤t) (hs : x≤s) :
    run front pulse t x = run front pulse s x := by
  simp only [front_run, ite_eq_right (by omega : x≠0), ite_eq_left ht, ite_eq_left hs]

/-- Causality in the time input, for every radius-one automaton. -/
theorem run_pulse_prefix (M : Automaton) (pulse pulse' : ℕ → Bool) (t : ℕ)
    (hp : ∀ s, s<t → pulse s=pulse' s) (x : ℕ) :
    run M pulse t x=run M pulse' t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih =>
    have hpre : ∀ s, s<t → pulse s=pulse' s := fun s hs => hp s (by omega)
    simp only [run, ih hpre, hp t (by omega)]

lemma period_prefix (q : ℕ) (_hq : 0<q) (s : ℕ) (hs : s<q) :
    decide (q ∣ s)=decide (s=0) := by
  by_cases hz : s=0
  · simp [hz]
  · simp [hz, Nat.not_dvd_of_pos_of_lt (by omega : 0<s) hs]

/-- Before the first positive pulse, all positive periods give the same run. -/
theorem run_period_prefix (M : Automaton) (q q' t x : ℕ)
    (hq : 0<q) (hq' : 0<q') (ht : t≤q) (ht' : t≤q') :
    run M (fun s => decide (q ∣ s)) t x =
      run M (fun s => decide (q' ∣ s)) t x := by
  apply run_pulse_prefix
  intro s hs
  rw [period_prefix q hq s (by omega), period_prefix q' hq' s (by omega)]

/-- The first period is an immutable unary input: a true mark at 1, q-1 false
cells, and a true mark at q+1. This is data for a later computation track. -/
theorem front_period_input (q : ℕ) (hq : 0<q) (t : ℕ) (ht : q+1≤t) :
    run front (fun s => decide (q ∣ s)) t 1=4 ∧
    (∀ x, 1<x → x≤q → run front (fun s => decide (q ∣ s)) t x=3) ∧
    run front (fun s => decide (q ∣ s)) t (q+1)=4 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [front_run, show 1≤t by omega, pulseSymbol]
  · intro x hx hxq
    have hn : ¬ q ∣ x-1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    simp [front_run, show x≠0 by omega, show x≤t by omega, hn, pulseSymbol]
  · simp [front_run, ht, pulseSymbol]

#print axioms front_period_input
#print axioms front_run
#print axioms front_frozen
#print axioms run_pulse_prefix
#print axioms run_period_prefix
end Sigma2.SimulatorFront




