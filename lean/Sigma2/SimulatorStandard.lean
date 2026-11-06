import Sigma2.SimulatorLoader
import Sigma2.SimulatorUnary

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorStandard
open Turing Sigma2.Tree Sigma2.SimulatorLocal Sigma2.SimulatorFold Sigma2.SimulatorLoader

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]
  [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]

lemma emit_running (M : TM0.Machine Γ Q) (a z : Γ)
    (l : Option (SimulatorTracks.State Γ Q)) (c r : SimulatorTracks.State Γ Q) (b : Bool)
    (ha : SimulatorReject.alarm M c=true) :
    update M a (l.map (fun s => (none,s))) (none,c) (none,r) b = (rule M a z).reject := by
  rw [update_running]
  simp [SimulatorReject.monitoredUpdate, ha, rule]

/-- On the actual prescribed seed, absence of symbol 2 is equivalent to
nontermination on the pulse-loaded unary tape. -/
theorem no_reject_iff (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q) :
    (∀ t x, run (automaton M a z) (fun s => decide (q ∣ s)) t x ≠ 2) ↔
      ¬ (TM0.eval M (z :: List.replicate q a)).Dom := by
  classical
  constructor
  · intro hno hdom
    have hh := (SimulatorReject.eval_dom_iff M (z :: List.replicate q a)).mp hdom
    let s := Nat.find hh
    have hs : TM0.step M ((advance M)^[s] (0, TM0.init (z :: List.replicate q a))).2 = none :=
      Nat.find_spec hh
    have hpre : ∀ j<s, TM0.step M ((advance M)^[j]
        (0, TM0.init (z :: List.replicate q a))).2 ≠ none := fun j hj => Nat.find_min hh hj
    have he := safe_simulation M a z q hq s hpre
    obtain ⟨x, hx⟩ := SimulatorReject.alarm_exists M
      ((advance M)^[s] (0, TM0.init (z :: List.replicate q a)))
      (fun x => run SimulatorFront.front (fun t => decide (q ∣ t)) (2*q+3+s) x) hs
    have htwo : SimulatorAlphabet.typedRun (rule M a z) (fun t => decide (q ∣ t))
        ((2*q+3+s)+1) x = (rule M a z).reject := by
      change update M a _ _ _ _ = _
      simp only [he]
      have hh := emit_running M a z
        (if x=0 then none else some
          (runningSnapshot M a z (fun t => decide (q ∣ t)) q (2*q+3) s (x-1)).2)
        (runningSnapshot M a z (fun t => decide (q ∣ t)) q (2*q+3) s x).2
        (runningSnapshot M a z (fun t => decide (q ∣ t)) q (2*q+3) s (x+1)).2
        (decide (q ∣ (2*q+3+s))) hx
      simpa only [apply_ite, Option.map_none, Option.map_some, runningSnapshot] using hh
    have hr := run_encode (rule M a z) (fun t => decide (q ∣ t)) ((2*q+3+s)+1) x
    rw [htwo, SimulatorAlphabet.encode_reject] at hr
    exact hno _ x hr.symm
  · intro hdom t x ht
    by_cases hload : t<2*q+3
    · exact initial_safe M a z q hq t x hload ht
    · have he : t=2*q+3+(t-(2*q+3)) := by omega
      have hpre : ∀ j<t-(2*q+3), TM0.step M ((advance M)^[j]
          (0, TM0.init (z :: List.replicate q a))).2 ≠ none := by
        intro j _ hj
        exact hdom ((SimulatorReject.eval_dom_iff M _).mpr ⟨j,hj⟩)
      have hsim := safe_simulation M a z q hq (t-(2*q+3)) hpre x
      have hd := SimulatorAlphabet.decode_run (rule M a z) (fun s => decide (q ∣ s)) t x
      change SimulatorAlphabet.decode (rule M a z) (run (automaton M a z) _ t x) = _ at hd
      rw [ht, SimulatorAlphabet.decode_two, he, hsim] at hd
      have hf := congrArg (fun s : State Γ Q => s.2.1) hd
      exact SimulatorReject.front_ne_two _ _ x hf.symm

open PartrecToTM2 in
/-- One ordinary data cell of the compiled four-stack tape. -/
def unaryBody : SimulatorMachine.TapeAlphabet :=
  (false, Function.update (fun _ => none) K'.main (some Γ'.bit1))

open PartrecToTM2 in
/-- The bottom mark and the list separator in the exact stack encoding. -/
def unaryBottom : SimulatorMachine.TapeAlphabet :=
  (true, Function.update (fun _ => none) K'.main (some Γ'.cons))

/-- The physical tape produced by the loader is exactly Mathlib's input,
including its reversed-stack and bottom-mark conventions. -/
theorem input_ones (q : ℕ) :
    SimulatorMachine.input [SimulatorUnary.ones q] = unaryBottom :: List.replicate q unaryBody := by
  simp [SimulatorMachine.input, PartrecToTM2.trList, SimulatorUnary.trNat_ones,
    TM2to1.trInit, unaryBottom, unaryBody, List.reverse_append]

/-- Loader, finite verifier, folded two-way simulation, exact rejection,
initial safety and the blank cone, assembled for every fixed parameter.
Uniform computability of the chosen transition tables is a separate obligation. -/
theorem program_exists (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) :
    ∃ A : Automaton, Sigma2.Reduction.ProgramCorrect R e A := by
  classical
  obtain ⟨Q, hQ, iQ, M, hM⟩ := SimulatorUnary.finite_unary_verifier R hR e
  letI := hQ
  letI := iQ
  letI : DecidableEq Q := Classical.decEq Q
  refine ⟨automaton M unaryBody unaryBottom, ?_, ?_, ?_⟩
  · intro q hq
    rw [no_reject_iff M unaryBody unaryBottom q hq, ← input_ones, hM q, not_not]
  · intro q hq t ht x
    exact initial_safe M unaryBody unaryBottom q hq t x (by omega)
  · intro pulse t x htx
    exact run_blank _ pulse t x htx

/-- Each fixed-parameter standard-seed program has the existing raw code
roundtrip; this theorem asserts no computability of the family of codes. -/
theorem code_exists (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) :
    ∃ c : ℕ, Sigma2.Reduction.ProgramCorrect R e (Sigma2.Reduction.decodeAutomaton c) := by
  obtain ⟨A,hA⟩ := program_exists R hR e
  refine ⟨SimulatorEncoding.code A, ?_⟩
  rwa [SimulatorEncoding.decode_code]

#print axioms no_reject_iff
#print axioms input_ones
#print axioms program_exists
#print axioms code_exists
end Sigma2.SimulatorStandard
