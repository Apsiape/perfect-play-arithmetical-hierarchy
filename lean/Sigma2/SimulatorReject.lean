import Sigma2.SimulatorTracks
import Sigma2.SimulatorVerifier

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace Sigma2.SimulatorReject
open Turing Sigma2.Tree Sigma2.SimulatorLocal Sigma2.SimulatorFold Sigma2.SimulatorTracks

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]

/-- A halted head is locally recognizable from its state and scanned symbol. -/
def cellHalted (M : TM0.Machine Γ Q) (c : Cell Γ Q) : Bool :=
  match c.2 with
  | none => false
  | some q => (M q c.1).isNone

def alarm (M : TM0.Machine Γ Q) (c : State Γ Q) : Bool :=
  cellHalted M c.2.1 || cellHalted M c.2.2

lemma cellHalted_picture (M : TM0.Machine Γ Q) (c : Positioned Γ Q) (z : ℤ) :
    cellHalted M (picture c z) =
      if z=c.1 then (M c.2.q c.2.Tape.head).isNone else false := by
  by_cases hz : z=c.1 <;> simp [cellHalted, picture, hz]

lemma step_none_iff (M : TM0.Machine Γ Q) (c : TM0.Cfg Γ Q) :
    TM0.step M c = none ↔ M c.q c.Tape.head = none := by
  cases c
  simp [TM0.step]

lemma alarm_false (M : TM0.Machine Γ Q) (c : Positioned Γ Q) (a : Fin 5) (x : ℕ)
    (hc : TM0.step M c.2 ≠ none) : alarm M (a, fold (picture c) x) = false := by
  have hm : (M c.2.q c.2.Tape.head).isNone = false := by
    cases h : M c.2.q c.2.Tape.head <;> simp_all [step_none_iff]
  simp [alarm, fold, cellHalted_picture, hm]

lemma alarm_exists (M : TM0.Machine Γ Q) (c : Positioned Γ Q) (a : ℕ → Fin 5)
    (hc : TM0.step M c.2 = none) : ∃ x, alarm M (a x, fold (picture c) x) = true := by
  have hm := (step_none_iff M c.2).mp hc
  rcases c with ⟨p, q, T⟩
  cases p with
  | ofNat n =>
    refine ⟨n, ?_⟩
    simp [alarm, fold, cellHalted_picture, hm]
  | negSucc n =>
    refine ⟨n, ?_⟩
    have hn : -(n : ℤ)-1 = Int.negSucc n := by omega
    simp [alarm, fold, cellHalted_picture, hn, hm]

lemma front_ne_two (pulse : ℕ → Bool) (t x : ℕ) :
    run SimulatorFront.front pulse t x ≠ 2 := by
  simp only [SimulatorFront.front_run, SimulatorFront.pulseSymbol]
  split_ifs <;> decide

/-- Rejection is absorbing and uses the exact distinguished symbol. -/
def monitoredUpdate (M : TM0.Machine Γ Q) (l : Option (State Γ Q))
    (c r : State Γ Q) (b : Bool) : State Γ Q :=
  if c.1=2 ∨ alarm M c=true then reject else update M l c r b

def monitoredRule (M : TM0.Machine Γ Q) : SimulatorAlphabet.Rule (State Γ Q) :=
  { rule M with
    update := monitoredUpdate M
    quiescence := by
      intro b
      change monitoredUpdate M (some blank) blank blank b = blank
      simp [monitoredUpdate, alarm, cellHalted, blank, vacant, update,
        halfRule, localRule, written, stationary, incoming] }

/-- Positioned evolution contains only genuine Mathlib reachable configurations. -/
theorem advance_reaches (M : TM0.Machine Γ Q) (c : Positioned Γ Q) (t : ℕ) :
    StateTransition.Reaches (TM0.step M) c.2 ((advance M)^[t] c).2 := by
  induction t with
  | zero => exact Relation.ReflTransGen.refl
  | succ t ih =>
    rw [Function.iterate_succ_apply', advance_cfg]
    cases hs : TM0.step M ((advance M)^[t] c).2 with
    | none => exact ih
    | some b => exact ih.tail hs

/-- Exact operational termination criterion, without a runtime bound. -/
theorem eval_dom_iff (M : TM0.Machine Γ Q) (v : List Γ) :
    (TM0.eval M v).Dom ↔
      ∃ t, TM0.step M ((advance M)^[t] (0, TM0.init v)).2 = none := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp h
    obtain ⟨t, hh, _⟩ := eventual_output M v w hw
    exact ⟨t, hh⟩
  · rintro ⟨t, ht⟩
    have hm := StateTransition.mem_eval.mpr ⟨advance_reaches M (0, TM0.init v) t, ht⟩
    exact (Part.mem_map_iff _).mpr ⟨_, hm, rfl⟩ |>.1

variable [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]

def automaton (M : TM0.Machine Γ Q) : Automaton :=
  SimulatorAlphabet.automaton (monitoredRule M)

def evolution (M : TM0.Machine Γ Q) (pulse : ℕ → Bool) (c : Positioned Γ Q)
    (t x : ℕ) : Symbol (automaton M) :=
  SimulatorAlphabet.runFrom (automaton M) pulse
    (fun y => SimulatorAlphabet.encode (monitoredRule M) (snapshot M pulse c 0 y)) t x

/-- Before the first halt, the monitored CA retains the exact joint snapshot. -/
theorem safe_simulation (M : TM0.Machine Γ Q) (pulse : ℕ → Bool) (c : Positioned Γ Q) :
    ∀ t, (∀ s<t, TM0.step M ((advance M)^[s] c).2 ≠ none) → ∀ x,
      SimulatorAlphabet.decode (monitoredRule M) (evolution M pulse c t x) =
        snapshot M pulse c t x := by
  intro t
  induction t with
  | zero => intro _ x; exact SimulatorAlphabet.decode_encode (monitoredRule M) _
  | succ t ih =>
    intro h x
    have he := ih (fun s hs => h s (by omega))
    simp only [evolution] at he
    have ha : alarm M (snapshot M pulse c t x) = false :=
      alarm_false M ((advance M)^[t] c) _ x (h t (by omega))
    have hn : (snapshot M pulse c t x).1 ≠ 2 := front_ne_two pulse t x
    change SimulatorAlphabet.decode (monitoredRule M)
      ((SimulatorAlphabet.automaton (monitoredRule M)).update _ _ _ _) = _
    rw [SimulatorAlphabet.decode_update]
    change monitoredUpdate M _ _ _ _ = _
    simp only [apply_ite, Option.map_none, Option.map_some, he]
    rw [monitoredUpdate, if_neg (show ¬ ((snapshot M pulse c t x).1=2 ∨
      alarm M (snapshot M pulse c t x)=true) by simp [ha, hn])]
    exact snapshot_step M pulse c t x

/-- A local halted-head alarm emits the actual paper symbol 2 on the next tick. -/
theorem emit_if_alarm (M : TM0.Machine Γ Q) (l : Option (Symbol (automaton M)))
    (c r : Symbol (automaton M)) (b : Bool)
    (hc : alarm M (SimulatorAlphabet.decode (monitoredRule M) c) = true) :
    (automaton M).update l c r b = 2 := by
  change (if l=some 1 ∧ c=1 ∧ r=1 then 1 else _) = 2
  split_ifs with h
  · rcases h with ⟨rfl, rfl, rfl⟩
    simp [SimulatorAlphabet.decode_one, monitoredRule, rule, blank, vacant, alarm, cellHalted] at hc
  · change SimulatorAlphabet.encode (monitoredRule M) (monitoredUpdate M _ _ _ _) = 2
    have he : monitoredUpdate M (l.map (SimulatorAlphabet.decode (monitoredRule M)))
        (SimulatorAlphabet.decode (monitoredRule M) c)
        (SimulatorAlphabet.decode (monitoredRule M) r) b = reject := by
      simp [monitoredUpdate, hc]
    rw [he]
    exact SimulatorAlphabet.encode_reject (monitoredRule M)

/-- For a prepared input, absence of the exact rejection symbol is equivalent
to nontermination of the machine, in both directions. -/
theorem no_reject_iff (M : TM0.Machine Γ Q) (pulse : ℕ → Bool) (v : List Γ) :
    (∀ t x, evolution M pulse (0, TM0.init v) t x ≠ 2) ↔ ¬ (TM0.eval M v).Dom := by
  classical
  constructor
  · intro hno hdom
    have hh := (eval_dom_iff M v).mp hdom
    let t := Nat.find hh
    have ht : TM0.step M ((advance M)^[t] (0, TM0.init v)).2 = none := Nat.find_spec hh
    have hpre : ∀ s<t, TM0.step M ((advance M)^[s] (0, TM0.init v)).2 ≠ none :=
      fun s hs => Nat.find_min hh hs
    have he := safe_simulation M pulse (0, TM0.init v) t hpre
    obtain ⟨x, hx⟩ := alarm_exists M ((advance M)^[t] (0, TM0.init v))
      (fun x => run SimulatorFront.front pulse t x) ht
    have hx' : alarm M (SimulatorAlphabet.decode (monitoredRule M)
        (evolution M pulse (0, TM0.init v) t x)) = true := by
      rw [he]
      exact hx
    have hn : evolution M pulse (0, TM0.init v) (t+1) x = 2 := by
      change (automaton M).update _ _ _ _ = 2
      exact emit_if_alarm M _ _ _ _ hx'
    exact hno (t+1) x hn
  · intro hdom t x htwo
    have hpre : ∀ s<t, TM0.step M ((advance M)^[s] (0, TM0.init v)).2 ≠ none := by
      intro s _ hs
      exact hdom ((eval_dom_iff M v).mpr ⟨s,hs⟩)
    have he := safe_simulation M pulse (0, TM0.init v) t hpre x
    rw [htwo, SimulatorAlphabet.decode_two] at he
    have hp := congrArg Prod.fst he
    exact front_ne_two pulse t x hp.symm

instance tapeAlphabetDecidableEq : DecidableEq SimulatorMachine.TapeAlphabet := Classical.decEq _

/-- A concrete finite-symbol CA recognizes every sequential verifier from an
already loaded e,q input. This does not assert pulse-driven loading or a
computable family of the initialized automata. -/
theorem prepared_verifier (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Inhabited Q) (_ : DecidableEq Q)
      (M : TM0.Machine SimulatorMachine.TapeAlphabet Q),
      ∀ (pulse : ℕ → Bool) (v : List.Vector ℕ 2),
        (∀ t x, evolution M pulse (0, TM0.init (SimulatorMachine.input v.val)) t x ≠ 2) ↔
          ∃ n, Sigma2.Reduction.PrimeRank n v.tail.head ∧ ∀ t, R (v.head,n,t)=true := by
  classical
  obtain ⟨Q, hQ, iQ, M, hM⟩ := SimulatorVerifier.finite_verifier R hR
  letI := hQ
  letI := iQ
  letI : DecidableEq Q := Classical.decEq Q
  refine ⟨Q, hQ, iQ, inferInstance, M, ?_⟩
  intro pulse v
  rw [no_reject_iff, hM v, not_not]

/-- A natural code in the unchanged reduction decoder. -/
theorem decode_code (M : TM0.Machine Γ Q) :
    Sigma2.Reduction.decodeAutomaton (Sigma2.SimulatorEncoding.code (automaton M)) =
      automaton M := Sigma2.SimulatorEncoding.decode_code _

/-- The assembled prepared-input result, stated entirely with an actual finite
CA, its natural code, and an explicit family of initial configurations. The
seed still contains e and q; replacing it by Tree.run's standard seed is open. -/
theorem prepared_automaton (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ A : Automaton,
      Sigma2.Reduction.decodeAutomaton (Sigma2.SimulatorEncoding.code A) = A ∧
      ∃ seed : ℕ → ℕ → ℕ → Symbol A, ∀ e q,
        (∀ t x, SimulatorAlphabet.runFrom A (fun s => decide (q ∣ s)) (seed e q) t x ≠ 2) ↔
          ∃ n, Sigma2.Reduction.PrimeRank n q ∧ ∀ t, R (e,n,t)=true := by
  classical
  obtain ⟨Q, hQ, iQ, dQ, M, hM⟩ := prepared_verifier R hR
  letI := hQ
  letI := iQ
  letI := dQ
  refine ⟨automaton M, decode_code M, ?_⟩
  refine ⟨fun e q y => SimulatorAlphabet.encode (monitoredRule M)
    (snapshot M (fun _ => false) (0, TM0.init (SimulatorMachine.input [e,q])) 0 y), ?_⟩
  intro e q
  have hh := hM (fun s => decide (q ∣ s)) (⟨[e,q], rfl⟩ : List.Vector ℕ 2)
  change (∀ t x, evolution M (fun s => decide (q ∣ s))
      (0, TM0.init (SimulatorMachine.input [e,q])) t x ≠ 2) ↔
    ∃ n, Sigma2.Reduction.PrimeRank n q ∧ ∀ t, R (e,n,t)=true at hh
  simpa only [evolution, snapshot, Function.iterate_zero_apply, run] using hh

#print axioms alarm_exists
#print axioms advance_reaches
#print axioms eval_dom_iff
#print axioms safe_simulation
#print axioms emit_if_alarm
#print axioms no_reject_iff
#print axioms prepared_verifier
#print axioms decode_code
#print axioms prepared_automaton
end Sigma2.SimulatorReject
