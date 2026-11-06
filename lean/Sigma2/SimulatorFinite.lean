import Sigma2.SimulatorMachine

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace Sigma2.SimulatorFinite
open Turing

variable {Γ Λ : Type} [Inhabited Γ] [Inhabited Λ] [DecidableEq Λ]
instance supportInhabited (S : Finset Λ) [Fact ((default : Λ) ∈ S)] : Inhabited {q // q ∈ S} :=
  ⟨⟨default, Fact.out⟩⟩

variable (M : TM0.Machine Γ Λ) (S : Finset Λ) [Fact ((default : Λ) ∈ S)]
variable (hs : TM0.Supports M (S : Set Λ))

/-- The initial state belongs to the closed finite support. -/
def initial : {q // q ∈ S} := ⟨default, hs.1⟩


/-- Retraction onto the reachable support; unreachable states go to the entry. -/
def retract (q : Λ) : {q // q ∈ S} :=
  if h : q ∈ S then ⟨q,h⟩ else initial M S hs

lemma retract_val (q : Λ) (hq : q ∈ S) : (retract M S hs q).val = q := by
  simp [retract, hq]

/-- A genuinely finite-state machine, using exactly Mathlib's transition map. -/
def machine : TM0.Machine Γ {q // q ∈ S} :=
  M.map (⟨id, rfl⟩ : PointedMap Γ Γ) (⟨id, rfl⟩ : PointedMap Γ Γ) (retract M S hs) Subtype.val

def translate : TM0.Cfg Γ Λ → TM0.Cfg Γ {q // q ∈ S} :=
  TM0.Cfg.map (⟨id, rfl⟩ : PointedMap Γ Γ) (retract M S hs)

lemma translate_tape (c : TM0.Cfg Γ Λ) : (translate M S hs c).Tape = c.Tape := by
  cases c with
  | mk q T =>
    cases T
    dsimp [translate, TM0.Cfg.map, Tape.map]
    congr 1 <;> apply ListBlank.ext <;> intro n <;> simp [ListBlank.nth_map]

/-- One step is preserved exactly on every supported configuration. -/
theorem step_exact (c : TM0.Cfg Γ Λ) (hc : c.q ∈ S) :
    (TM0.step M c).map (translate M S hs) =
      TM0.step (machine M S hs) (translate M S hs c) := by
  apply TM0.Machine.map_step
  · intro a; rfl
  · exact fun q hq => retract_val M S hs q hq
  · exact hc

/-- No extra halting behavior is introduced by restricting the state set. -/
theorem respects : StateTransition.Respects (TM0.step M) (TM0.step (machine M S hs))
    (fun c d => c.q ∈ S ∧ translate M S hs c = d) := by
  apply TM0.Machine.map_respects M (⟨id, rfl⟩ : PointedMap Γ Γ) (⟨id, rfl⟩ : PointedMap Γ Γ)
    ⟨retract M S hs, by apply Subtype.ext; exact retract_val M S hs default Fact.out⟩ Subtype.val hs
  · intro a; rfl
  · exact fun q hq => retract_val M S hs q hq

lemma translate_init (v : List Γ) :
    translate M S hs (TM0.init v) = TM0.init v := by
  have h := TM0.map_init (⟨id, rfl⟩ : PointedMap Γ Γ)
    (⟨retract M S hs, by apply Subtype.ext; exact retract_val M S hs default Fact.out⟩ : PointedMap Λ {q // q ∈ S}) v
  simpa [translate] using h

/-- The finite restriction preserves the exact output tape in both directions. -/
theorem eval_exact (v : List Γ) : TM0.eval (machine M S hs) v = TM0.eval M v := by
  apply Part.ext
  intro w
  simp only [TM0.eval, Part.mem_map_iff]
  constructor
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨c, hc, he⟩ := StateTransition.tr_eval_rev (respects M S hs)
      (show (TM0.init v).q ∈ S ∧ translate M S hs (TM0.init v) = TM0.init v from
        ⟨hs.1, translate_init M S hs v⟩) hd
    refine ⟨c, he, ?_⟩
    rw [← hc.2, translate_tape]
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨d, hd, he⟩ := StateTransition.tr_eval (respects M S hs)
      (show (TM0.init v).q ∈ S ∧ translate M S hs (TM0.init v) = TM0.init v from
        ⟨hs.1, translate_init M S hs v⟩) hc
    refine ⟨d, he, ?_⟩
    rw [← hd.2, translate_tape]

/-- Every extracted predicate program has a genuinely finite state type and the
same exact Boolean output. This is an existence result, not a uniform compiler. -/
theorem predicate_finite_machine (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Inhabited Q)
      (N : TM0.Machine SimulatorMachine.TapeAlphabet Q),
      ∀ v : List.Vector ℕ 3, ∃ w ∈ TM0.eval N (SimulatorMachine.input v.val),
        SimulatorMachine.OutputEncodes w [SimulatorMachine.result R v] := by
  classical
  obtain ⟨c, hc⟩ := SimulatorMachine.computable_predicate_machine R hR
  letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  obtain ⟨S, hs⟩ := SimulatorMachine.finite_support c
  let M := TM1to0.tr SimulatorMachine.machine1
  letI : Fact ((default : SimulatorMachine.Labels0) ∈ S) := ⟨hs.1⟩
  refine ⟨{q // q ∈ S}, inferInstance, inferInstance, machine M S hs, ?_⟩
  intro v
  obtain ⟨w, hw, ho⟩ := hc v
  refine ⟨w, ?_, ho⟩
  rw [eval_exact M S hs]
  exact hw

#print axioms step_exact
#print axioms eval_exact
#print axioms predicate_finite_machine
end Sigma2.SimulatorFinite
