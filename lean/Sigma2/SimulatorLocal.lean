import Sigma2.SimulatorMachine
import Sigma2.SimulatorFront

noncomputable section
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorLocal
open Turing

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]

abbrev Cell (Γ Q : Type) := Γ × Option Q

/-- A position is retained explicitly while Mathlib's tape stays head-relative. -/
abbrev Positioned (Γ Q : Type) [Inhabited Γ] := ℤ × TM0.Cfg Γ Q

def picture (c : Positioned Γ Q) (z : ℤ) : Cell Γ Q :=
  (c.2.Tape.nth (z-c.1), if z=c.1 then some c.2.q else none)

def stationary (M : TM0.Machine Γ Q) (c : Cell Γ Q) : Option Q :=
  match c.2 with
  | none => none
  | some q => match M q c.1 with
    | none => some q
    | some (q', .write _) => some q'
    | some (_, .move _) => none

def incoming (M : TM0.Machine Γ Q) (d : Dir) (c : Cell Γ Q) : Option Q :=
  match c.2 with
  | none => none
  | some q => match M q c.1 with
    | some (q', .move d') => if d'=d then some q' else none
    | _ => none

def written (M : TM0.Machine Γ Q) (c : Cell Γ Q) : Γ :=
  match c.2 with
  | none => c.1
  | some q => match M q c.1 with
    | some (_, .write a) => a
    | _ => c.1

/-- Radius-one head transport. Malformed multiple-head inputs are resolved by
center, left, right priority; the simulation theorem uses exactly one head. -/
def localRule (M : TM0.Machine Γ Q) (l c r : Cell Γ Q) : Cell Γ Q :=
  (written M c, (stationary M c).or ((incoming M .right l).or (incoming M .left r)))

def lineStep (M : TM0.Machine Γ Q) (v : ℤ → Cell Γ Q) (z : ℤ) : Cell Γ Q :=
  localRule M (v (z-1)) (v z) (v (z+1))

/-- A halted machine is kept stationary, allowing an ordinary total CA run. -/
def advance (M : TM0.Machine Γ Q) (c : Positioned Γ Q) : Positioned Γ Q :=
  match M c.2.q c.2.Tape.head with
  | none => c
  | some (q', .write a) => (c.1, ⟨q', c.2.Tape.write a⟩)
  | some (q', .move .left) => (c.1-1, ⟨q', c.2.Tape.move .left⟩)
  | some (q', .move .right) => (c.1+1, ⟨q', c.2.Tape.move .right⟩)

/-- The radius-one local rule executes one exact Mathlib TM0 step on the head/tape
picture, including halting, writes, and both directions of motion. -/
theorem lineStep_picture (M : TM0.Machine Γ Q) (c : Positioned Γ Q) :
    lineStep M (picture c) = picture (advance M c) := by
  rcases c with ⟨p, q, T⟩
  funext z
  cases hm : M q T.head with
  | none =>
    by_cases h0 : z=p <;> by_cases hl : z-1=p <;> by_cases hr : z+1=p <;>
      simp [lineStep, localRule, picture, advance, written, stationary, incoming, hm, h0, hl, hr]
  | some a =>
    rcases a with ⟨q', a⟩
    cases a with
    | write a =>
      by_cases h0 : z=p <;> by_cases hl : z-1=p <;> by_cases hr : z+1=p <;>
        simp [lineStep, localRule, picture, advance, written, stationary, incoming, hm, h0, hl, hr,
          Tape.write_nth, sub_eq_zero] <;> try rfl
    | move d =>
      cases d <;>
        by_cases h0 : z=p <;> by_cases hl : z-1=p <;> by_cases hr : z+1=p <;>
        (try omega)
      all_goals have hL : (z=p-1) ↔ (z+1=p) := by omega
      all_goals have hR : (z=p+1) ↔ (z-1=p) := by omega
      all_goals simp [lineStep, localRule, picture, advance, written, stationary, incoming,
        hm, h0, hl, hr, hL, hR, Tape.move_left_nth, Tape.move_right_nth, sub_eq_zero] <;>
        congr 1 <;> omega

/-- Forgetting the explicit position gives Mathlib's totalized step exactly. -/
theorem advance_cfg (M : TM0.Machine Γ Q) (c : Positioned Γ Q) :
    (advance M c).2 = (TM0.step M c.2).getD c.2 := by
  rcases c with ⟨p, q, T⟩
  cases hm : M q T.head with
  | none => simp [advance, TM0.step, hm]
  | some a =>
    rcases a with ⟨q', a⟩
    cases a with
    | write a => simp [advance, TM0.step, hm]
    | move d => cases d <;> simp [advance, TM0.step, hm]

/-- Every finite Mathlib execution is reached by the positioned evolution. -/
theorem reaches_advance (M : TM0.Machine Γ Q) (c : Positioned Γ Q)
    (b : TM0.Cfg Γ Q) (hb : StateTransition.Reaches (TM0.step M) c.2 b) :
    ∃ t, ((advance M)^[t] c).2 = b := by
  induction hb with
  | refl => exact ⟨0, rfl⟩
  | @tail a b h hab ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t+1, ?_⟩
    rw [Function.iterate_succ_apply', advance_cfg, ht, hab]
    rfl

/-- Halting and the exact output tape are eventually visible in the CA's
positioned computation; no execution-time bound is assumed. -/
theorem eventual_output (M : TM0.Machine Γ Q) (v : List Γ) (w : ListBlank Γ)
    (hw : w ∈ TM0.eval M v) :
    ∃ t, let c := (advance M)^[t] (0, TM0.init v)
      TM0.step M c.2 = none ∧ c.2.Tape.right₀ = w := by
  obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hw
  obtain ⟨hr, hh⟩ := StateTransition.mem_eval.mp hb
  obtain ⟨t, ht⟩ := reaches_advance M (0, TM0.init v) b hr
  exact ⟨t, by dsimp only; rw [ht]; exact ⟨hh, rfl⟩⟩

/-- There is exactly one encoded head at every time. -/
theorem unique_head (c : Positioned Γ Q) : ∃! z, (picture c z).2 ≠ none := by
  refine ⟨c.1, by simp [picture], ?_⟩
  intro z hz
  by_contra h
  exact hz (by simp [picture, h])

#print axioms lineStep_picture
#print axioms advance_cfg
#print axioms reaches_advance
#print axioms eventual_output
#print axioms unique_head
end Sigma2.SimulatorLocal

