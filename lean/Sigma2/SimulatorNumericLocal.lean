import Sigma2.SimulatorParameterKernel

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorNumericLocal
open Turing Sigma2.SimulatorNumbered Sigma2.SimulatorParameter Sigma2.SimulatorParameterCoding
  Sigma2.SimulatorParameterKernel Sigma2.SimulatorLocal

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q]

abbrev CellRep (Γ : Type) := Γ × Option ℕ
abbrev StateRep (Γ : Type) := Option SimulatorLoader.Control × Fin 5 × (CellRep Γ × CellRep Γ)

def cellRep (e : ℕ) (c : Cell Γ (Label e Q)) : CellRep Γ :=
  (c.1,c.2.map (labelCoding (Coding.fixed Q) e).enc)
def cellDec (e : ℕ) (c : CellRep Γ) : Cell Γ (Label e Q) :=
  (c.1,c.2.map (labelCoding (Coding.fixed Q) e).dec)
def stateRep (e : ℕ) (s : SimulatorLoader.State Γ (Label e Q)) : StateRep Γ :=
  (s.1,(s.2.1,(cellRep e s.2.2.1,cellRep e s.2.2.2)))
def stateDec (e : ℕ) (s : StateRep Γ) : SimulatorLoader.State Γ (Label e Q) :=
  (s.1,(s.2.1,(cellDec e s.2.2.1,cellDec e s.2.2.2)))

lemma cellDec_rep (e : ℕ) (c : Cell Γ (Label e Q)) : cellDec e (cellRep e c)=c := by
  rcases c with ⟨s,q⟩
  cases q <;> simp [cellDec, cellRep]
lemma stateDec_rep (e : ℕ) (s : SimulatorLoader.State Γ (Label e Q)) :
    stateDec e (stateRep e s)=s := by
  simp [stateDec, stateRep, cellDec_rep]
lemma stateRep_injective (e : ℕ) : Function.Injective (stateRep (Γ:=Γ) (Q:=Q) e) :=
  Function.LeftInverse.injective (stateDec_rep e)

def isWrite : TM0.Stmt Γ → Bool | .write _ => true | .move _ => false
def writeValue : TM0.Stmt Γ → Γ | .write s => s | .move _ => default
def isMove (d : Dir) : TM0.Stmt Γ → Bool
  | .write _ => false | .move d' => decide (d'=d)

variable (M : TM0.Machine Γ Q) (a z sep : Γ)

def writtenNum (e : ℕ) (c : CellRep Γ) : Γ :=
  match c.2 with
  | none => c.1
  | some k => ((transition M a z sep e (k,c.1)).map
      (fun p => if isWrite p.2 then writeValue p.2 else c.1)).getD c.1

def stationaryNum (e : ℕ) (c : CellRep Γ) : Option ℕ :=
  match c.2 with
  | none => none
  | some k => (transition M a z sep e (k,c.1)).casesOn
      (some (normalize (Q:=Q) e k))
      (fun p => if isWrite p.2 then some p.1 else none)

def incomingNum (d : Dir) (e : ℕ) (c : CellRep Γ) : Option ℕ :=
  match c.2 with
  | none => none
  | some k => (transition M a z sep e (k,c.1)).bind
      (fun p => if isMove d p.2 then some p.1 else none)

def localNum (e : ℕ) (l c r : CellRep Γ) : CellRep Γ :=
  (writtenNum M a z sep e c,
    (stationaryNum M a z sep e c).or
      ((incomingNum M a z sep .right e l).or (incomingNum M a z sep .left e r)))

lemma written_eq (e : ℕ) (c : CellRep Γ) :
    written (machine M a z sep e) (cellDec (Q:=Q) e c)=writtenNum M a z sep e c := by
  rcases c with ⟨s,q⟩
  cases q with
  | none => rfl
  | some k =>
    cases h : machine M a z sep e ((labelCoding (Coding.fixed Q) e).dec k) s with
    | none => simp [written, cellDec, writtenNum, transition, h]
    | some p =>
      rcases p with ⟨q,d|s'⟩
      · simp [written, cellDec, writtenNum, transition, h, isWrite]
      · simp [written, cellDec, writtenNum, transition, h, isWrite, writeValue]

lemma stationary_eq (e : ℕ) (c : CellRep Γ) :
    (stationary (machine M a z sep e) (cellDec (Q:=Q) e c)).map
      (labelCoding (Coding.fixed Q) e).enc=stationaryNum M a z sep e c := by
  rcases c with ⟨s,q⟩
  cases q with
  | none => rfl
  | some k =>
    cases h : machine M a z sep e ((labelCoding (Coding.fixed Q) e).dec k) s with
    | none => simp [stationary, cellDec, stationaryNum, transition, SimulatorParameterKernel.normalize, h]
    | some p =>
      rcases p with ⟨q,d|s'⟩
      · simp [stationary, cellDec, stationaryNum, transition, h, isWrite]
      · simp [stationary, cellDec, stationaryNum, transition, h, isWrite]

lemma incoming_eq (d : Dir) (e : ℕ) (c : CellRep Γ) :
    (incoming (machine M a z sep e) d (cellDec (Q:=Q) e c)).map
      (labelCoding (Coding.fixed Q) e).enc=incomingNum M a z sep d e c := by
  rcases c with ⟨s,q⟩
  cases q with
  | none => rfl
  | some k =>
    cases h : machine M a z sep e ((labelCoding (Coding.fixed Q) e).dec k) s with
    | none => simp [incoming, cellDec, incomingNum, transition, h]
    | some p =>
      rcases p with ⟨q,d'|s'⟩
      · by_cases hd : d'=d <;> simp [incoming, cellDec, incomingNum, transition, h, isMove, hd]
      · simp [incoming, cellDec, incomingNum, transition, h, isMove]

lemma map_or {A B : Type} (f : A → B) (a b : Option A) :
    (a.or b).map f=(a.map f).or (b.map f) := by cases a <;> rfl

lemma local_eq (e : ℕ) (l c r : CellRep Γ) :
    cellRep e (localRule (machine M a z sep e)
      (cellDec (Q:=Q) e l) (cellDec e c) (cellDec e r))=localNum M a z sep e l c r := by
  simp only [cellRep, localRule, written_eq, map_or, stationary_eq, incoming_eq, localNum]

#print axioms local_eq
end Sigma2.SimulatorNumericLocal

