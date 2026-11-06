import Sigma2.SimulatorNumericLocal

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorNumericTracks
open Turing Sigma2.SimulatorNumbered Sigma2.SimulatorParameter Sigma2.SimulatorParameterCoding
  Sigma2.SimulatorParameterKernel Sigma2.SimulatorLocal Sigma2.SimulatorFold
  Sigma2.SimulatorNumericLocal

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q]
abbrev TrackRep (Γ : Type) := Fin 5 × (CellRep Γ × CellRep Γ)

def trackRep (e : ℕ) (s : SimulatorTracks.State Γ (Label e Q)) : TrackRep Γ :=
  (s.1,(cellRep e s.2.1,cellRep e s.2.2))
def trackDec (e : ℕ) (s : TrackRep Γ) : SimulatorTracks.State Γ (Label e Q) :=
  (s.1,(cellDec e s.2.1,cellDec e s.2.2))

variable (M : TM0.Machine Γ Q) (a z sep : Γ)

def haltedNum (e : ℕ) (c : CellRep Γ) : Bool :=
  match c.2 with
  | none => false
  | some k => (transition M a z sep e (k,c.1)).isNone

def alarmNum (e : ℕ) (c : TrackRep Γ) : Bool :=
  haltedNum M a z sep e c.2.1 || haltedNum M a z sep e c.2.2

def trackNum (e : ℕ) (l : Option (TrackRep Γ)) (c r : TrackRep Γ) (b : Bool) : TrackRep Γ :=
  (Sigma2.SimulatorFront.front.update (l.map Prod.fst) c.1 r.1 b,
    halfRule (localNum M a z sep e) (l.map Prod.snd) c.2 r.2)

def monitoredNum (e : ℕ) (l : Option (TrackRep Γ)) (c r : TrackRep Γ) (b : Bool) : TrackRep Γ :=
  if c.1=2 ∨ alarmNum M a z sep e c=true then (2,((default,none),(default,none)))
  else trackNum M a z sep e l c r b

def updateNum (e : ℕ) (l : Option (StateRep Γ)) (c r : StateRep Γ) (b : Bool) : StateRep Γ :=
  let d := SimulatorLoader.command (l.map Prod.fst) c.1 r.1 b
  let s := monitoredNum M a z sep e (l.map Prod.snd) c.2 r.2 b
  (d.1,(s.1,((if d.2.1 then (a,none) else if d.2.2 then
    (s.2.1.1,some ((labelCoding (Coding.fixed Q) e).enc default)) else s.2.1),s.2.2)))

lemma halted_eq (e : ℕ) (c : CellRep Γ) :
    SimulatorReject.cellHalted (machine M a z sep e) (cellDec (Q:=Q) e c)=
      haltedNum M a z sep e c := by
  rcases c with ⟨s,q⟩
  cases q with
  | none => rfl
  | some k =>
    cases h : machine M a z sep e ((labelCoding (Coding.fixed Q) e).dec k) s <;>
      simp [SimulatorReject.cellHalted, cellDec, haltedNum, transition, h]

lemma alarm_eq (e : ℕ) (c : TrackRep Γ) :
    SimulatorReject.alarm (machine M a z sep e) (trackDec (Q:=Q) e c)=
      alarmNum M a z sep e c := by
  simp only [SimulatorReject.alarm, trackDec, halted_eq, alarmNum]

lemma half_eq (e : ℕ) (l : Option (CellRep Γ × CellRep Γ))
    (c r : CellRep Γ × CellRep Γ) :
    let F := fun p : Cell Γ (Label e Q) × Cell Γ (Label e Q) => (cellRep e p.1,cellRep e p.2)
    F (halfRule (localRule (machine M a z sep e))
      (l.map (fun p => (cellDec e p.1,cellDec e p.2)))
      (cellDec e c.1,cellDec e c.2) (cellDec e r.1,cellDec e r.2)) =
      halfRule (localNum M a z sep e) l c r := by
  cases l <;> simp [halfRule, local_eq]

lemma track_eq (e : ℕ) (l : Option (TrackRep Γ)) (c r : TrackRep Γ) (b : Bool) :
    trackRep e (SimulatorTracks.update (machine M a z sep e)
      (l.map (trackDec (Q:=Q) e)) (trackDec e c) (trackDec e r) b)=
      trackNum M a z sep e l c r b := by
  cases l <;> simp [trackRep, trackDec, SimulatorTracks.update, trackNum, halfRule, local_eq]

lemma monitored_eq (e : ℕ) (l : Option (TrackRep Γ)) (c r : TrackRep Γ) (b : Bool) :
    trackRep e (SimulatorReject.monitoredUpdate (machine M a z sep e)
      (l.map (trackDec (Q:=Q) e)) (trackDec e c) (trackDec e r) b)=
      monitoredNum M a z sep e l c r b := by
  unfold SimulatorReject.monitoredUpdate monitoredNum
  rw [alarm_eq]
  dsimp only [trackDec]
  split_ifs
  · rfl
  · exact track_eq M a z sep e l c r b

lemma update_eq (e : ℕ) (l : Option (StateRep Γ)) (c r : StateRep Γ) (b : Bool) :
    stateRep e (SimulatorLoader.update (machine M a z sep e) a
      (l.map (stateDec (Q:=Q) e)) (stateDec e c) (stateDec e r) b)=
      updateNum M a z sep e l c r b := by
  unfold SimulatorLoader.update updateNum
  have hm := monitored_eq M a z sep e (l.map Prod.snd) c.2 r.2 b
  cases l <;> simp only [Option.map_some, Option.map_none, stateDec, Option.map_map] at *
  all_goals
    change stateRep e _ = _
    rw [← hm]
    dsimp only [stateRep, trackRep, cellRep]
    split_ifs <;> rfl

#print axioms update_eq
end Sigma2.SimulatorNumericTracks

