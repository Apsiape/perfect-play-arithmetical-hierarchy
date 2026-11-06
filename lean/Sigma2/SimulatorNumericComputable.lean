import Sigma2.SimulatorNumericEncoding

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorNumericComputable
open Turing Sigma2.Tree Sigma2.SimulatorNumbered Sigma2.SimulatorParameter Sigma2.SimulatorParameterCoding
  Sigma2.SimulatorParameterKernel Sigma2.SimulatorNumericLocal Sigma2.SimulatorNumericTracks
  Sigma2.SimulatorNumericEncoding

local instance : Nonempty SimulatorLoader.Control := ⟨.origin⟩
instance : Primcodable SimulatorLoader.Control :=
  Primcodable.ofEquiv (Fin (Fintype.card SimulatorLoader.Control)) (Fintype.equivFin _)

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q] [Fintype Γ] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q]
variable {α : Type} [Primcodable α]

@[fun_prop] theorem norm_comp (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => SimulatorParameterKernel.normalize (Q:=Q) (f x) (g x)) :=
  normalize_primrec.comp hf hg
@[fun_prop] theorem trans_comp (M : TM0.Machine Γ Q) (a z sep : Γ)
    (f : α → ℕ) (g : α → ℕ × Γ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => transition M a z sep (f x) (g x)) := transition_primrec M a z sep |>.comp hf hg
@[fun_prop] theorem isWrite_comp (f : α → TM0.Stmt Γ) (hf : Primrec f) :
    Primrec (fun x => isWrite (f x)) := (Primrec.dom_finite isWrite).comp hf
@[fun_prop] theorem writeValue_comp (f : α → TM0.Stmt Γ) (hf : Primrec f) :
    Primrec (fun x => writeValue (f x)) := (Primrec.dom_finite writeValue).comp hf
@[fun_prop] theorem isMove_comp (d : Dir) (f : α → TM0.Stmt Γ) (hf : Primrec f) :
    Primrec (fun x => isMove d (f x)) := (Primrec.dom_finite (isMove d)).comp hf

@[fun_prop] theorem optionNone_comp {β : Type} [Primcodable β]
    (f : α → Option β) (hf : Primrec f) : Primrec (fun x => (f x).isNone) := by
  have h : Primrec (fun o : Option β => o.isNone) := by
    have hg : Primrec (fun _ : Option β × β => false) := Primrec.const false
    have hh := Primrec.option_casesOn (show Primrec (@id (Option β)) from Primrec.id)
      (Primrec.const true) hg.to₂
    exact hh.of_eq (fun o => by cases o <;> rfl)
  exact h.comp hf

@[fun_prop] theorem or_comp (f g : α → Option ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => (f x).or (g x)) := by
  have h : Primrec₂ (@Option.or ℕ) := by
    have hs : Primrec (fun p : (Option ℕ × Option ℕ) × ℕ => some p.2) :=
      Primrec.option_some.comp Primrec.snd
    have hh := Primrec.option_casesOn
      (show Primrec (fun p : Option ℕ × Option ℕ => p.1) from Primrec.fst)
      (show Primrec (fun p : Option ℕ × Option ℕ => p.2) from Primrec.snd) hs.to₂
    exact hh.of_eq (fun p => by rcases p with ⟨o,v⟩; cases o <;> rfl)
  exact h.comp hf hg

@[fun_prop] theorem front_comp (l : α → Option (Fin 5)) (c r : α → Fin 5) (b : α → Bool)
    (hl : Primrec l) (hc : Primrec c) (hr : Primrec r) (hb : Primrec b) :
    Primrec (fun x => SimulatorFront.front.update (l x) (c x) (r x) (b x)) :=
  (Primrec.dom_finite (fun p : Option (Fin 5) × Fin 5 × Fin 5 × Bool =>
    SimulatorFront.front.update p.1 p.2.1 p.2.2.1 p.2.2.2)).comp
      (hl.pair (hc.pair (hr.pair hb)))
@[fun_prop] theorem command_comp (l : α → Option (Option SimulatorLoader.Control))
    (c r : α → Option SimulatorLoader.Control) (b : α → Bool)
    (hl : Primrec l) (hc : Primrec c) (hr : Primrec r) (hb : Primrec b) :
    Primrec (fun x => SimulatorLoader.command (l x) (c x) (r x) (b x)) :=
  (Primrec.dom_finite (fun p : Option (Option SimulatorLoader.Control) ×
      Option SimulatorLoader.Control × Option SimulatorLoader.Control × Bool =>
    SimulatorLoader.command p.1 p.2.1 p.2.2.1 p.2.2.2)).comp
      (hl.pair (hc.pair (hr.pair hb)))

variable (M : TM0.Machine Γ Q) (a z sep : Γ)

theorem written_primrec : Primrec (fun p : ℕ × CellRep Γ => writtenNum M a z sep p.1 p.2) := by
  unfold writtenNum
  have ht : Primrec (fun p : (ℕ × CellRep Γ) × ℕ =>
      transition M a z sep p.1.1 (p.2,p.1.2.1)) := by fun_prop
  have hv : Primrec (fun p : ((ℕ × CellRep Γ) × ℕ) × (ℕ × TM0.Stmt Γ) =>
      if isWrite p.2.2 then writeValue p.2.2 else p.1.1.2.1) := by fun_prop
  have hm := Primrec.option_map ht hv.to₂
  have hi := Primrec.option_getD.comp hm
    (show Primrec (fun p : (ℕ × CellRep Γ) × ℕ => p.1.2.1) from by fun_prop)
  have hh := Primrec.option_casesOn (Primrec.snd.comp Primrec.snd)
    (Primrec.fst.comp Primrec.snd) hi.to₂
  exact hh.of_eq (fun p => by rcases p with ⟨e,s,q⟩; cases q <;> rfl)

theorem stationary_primrec :
    Primrec (fun p : ℕ × CellRep Γ => stationaryNum M a z sep p.1 p.2) := by
  unfold stationaryNum
  have ht : Primrec (fun p : (ℕ × CellRep Γ) × ℕ =>
      transition M a z sep p.1.1 (p.2,p.1.2.1)) := by fun_prop
  have hn : Primrec (fun p : (ℕ × CellRep Γ) × ℕ =>
      some (SimulatorParameterKernel.normalize (Q:=Q) p.1.1 p.2)) := by fun_prop
  have hv : Primrec (fun p : ((ℕ × CellRep Γ) × ℕ) × (ℕ × TM0.Stmt Γ) =>
      if isWrite p.2.2 then some p.2.1 else none) := by fun_prop
  have hi := Primrec.option_casesOn ht hn hv.to₂
  have hh := Primrec.option_casesOn (Primrec.snd.comp Primrec.snd) (Primrec.const none) hi.to₂
  exact hh.of_eq (fun p => by rcases p with ⟨e,s,q⟩; cases q <;> rfl)

theorem incoming_primrec (d : Dir) :
    Primrec (fun p : ℕ × CellRep Γ => incomingNum M a z sep d p.1 p.2) := by
  unfold incomingNum
  have ht : Primrec (fun p : (ℕ × CellRep Γ) × ℕ =>
      transition M a z sep p.1.1 (p.2,p.1.2.1)) := by fun_prop
  have hv : Primrec (fun p : ((ℕ × CellRep Γ) × ℕ) × (ℕ × TM0.Stmt Γ) =>
      if isMove d p.2.2 then some p.2.1 else none) := by fun_prop
  have hi := Primrec.option_bind ht hv.to₂
  have hh := Primrec.option_casesOn (Primrec.snd.comp Primrec.snd) (Primrec.const none) hi.to₂
  exact hh.of_eq (fun p => by rcases p with ⟨e,s,q⟩; cases q <;> rfl)

theorem halted_primrec : Primrec (fun p : ℕ × CellRep Γ => haltedNum M a z sep p.1 p.2) := by
  unfold haltedNum
  have hi : Primrec (fun p : (ℕ × CellRep Γ) × ℕ =>
      (transition M a z sep p.1.1 (p.2,p.1.2.1)).isNone) := by fun_prop
  have hh := Primrec.option_casesOn (Primrec.snd.comp Primrec.snd) (Primrec.const false) hi.to₂
  exact hh.of_eq (fun p => by rcases p with ⟨e,s,q⟩; cases q <;> rfl)

@[fun_prop] theorem written_comp (f : α → ℕ) (g : α → CellRep Γ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => writtenNum M a z sep (f x) (g x)) :=
  (written_primrec M a z sep).comp (hf.pair hg)
@[fun_prop] theorem stationary_comp (f : α → ℕ) (g : α → CellRep Γ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => stationaryNum M a z sep (f x) (g x)) :=
  (stationary_primrec M a z sep).comp (hf.pair hg)
@[fun_prop] theorem incoming_comp (d : Dir) (f : α → ℕ) (g : α → CellRep Γ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => incomingNum M a z sep d (f x) (g x)) :=
  (incoming_primrec M a z sep d).comp (hf.pair hg)
@[fun_prop] theorem halted_comp (f : α → ℕ) (g : α → CellRep Γ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => haltedNum M a z sep (f x) (g x)) :=
  (halted_primrec M a z sep).comp (hf.pair hg)

#print axioms written_primrec
#print axioms stationary_primrec
#print axioms incoming_primrec
#print axioms halted_primrec
end Sigma2.SimulatorNumericComputable
