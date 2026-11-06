import Sigma2.SimulatorNumericComputable

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorEffectiveKernel
open Turing Sigma2.Tree Sigma2.SimulatorNumbered Sigma2.SimulatorParameter Sigma2.SimulatorParameterCoding
  Sigma2.SimulatorParameterKernel Sigma2.SimulatorNumericLocal Sigma2.SimulatorNumericTracks
  Sigma2.SimulatorNumericEncoding Sigma2.SimulatorNumericComputable

local instance : Nonempty SimulatorLoader.Control := ⟨.origin⟩
variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q] [Fintype Γ] [Fintype Q]
  [DecidableEq Γ] [DecidableEq Q] [Primcodable Γ] [Primcodable Q]
variable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]

@[fun_prop] theorem mapFixed_comp (g : β → σ) (f : α → Option β)
    (hg : Primrec g) (hf : Primrec f) : Primrec (fun x => (f x).map g) :=
  (Primrec.option_map₁ hg).comp hf
@[fun_prop] theorem getD_comp (f : α → Option β) (g : α → β)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => (f x).getD (g x)) :=
  Primrec.option_getD.comp hf hg

@[fun_prop] theorem headPack_comp (f : α → Option ℕ) (hf : Primrec f) :
    Primrec (fun x => headPack (f x)) :=
  (Primrec.option_getD.comp (Primrec.option_map₁ Primrec.succ) (Primrec.const 0)).comp hf
@[fun_prop] theorem headUnpack_comp (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun x => headUnpack (f x)) := by unfold headUnpack; fun_prop (maxSteps := 500)
@[fun_prop] theorem headSize_comp (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun x => headSize (Q:=Q) (f x)) := by
  unfold headSize labelCoding
  dsimp only
  fun_prop (maxSteps := 500)
@[fun_prop] theorem cellSize_comp (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun x => cellSize (Γ:=Γ) (Q:=Q) (f x)) := by unfold cellSize; fun_prop (maxSteps := 500)

@[fun_prop] theorem controlEnc_comp (f : α → Option SimulatorLoader.Control) (hf : Primrec f) :
    Primrec (fun x => (Coding.fixed SimulatorLoader.Control).option.enc (f x)) :=
  (Primrec.dom_finite (Coding.fixed SimulatorLoader.Control).option.enc).comp hf
@[fun_prop] theorem controlDec_comp (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun x => (Coding.fixed SimulatorLoader.Control).option.dec (f x)) := by
  unfold Coding.option
  dsimp only
  fun_prop (maxSteps := 500)

@[fun_prop] theorem cellPack_comp (f : α → ℕ) (g : α → CellRep Γ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => cellPack (Q:=Q) (f x) (g x)) := by
  unfold cellPack
  fun_prop (maxSteps := 500)
@[fun_prop] theorem cellUnpack_comp (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => cellUnpack (Γ:=Γ) (Q:=Q) (f x) (g x)) := by unfold cellUnpack; fun_prop (maxSteps := 500)
@[fun_prop] theorem pack_comp (f : α → ℕ) (g : α → StateRep Γ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => pack (Q:=Q) (f x) (g x)) := by
  unfold pack
  fun_prop (maxSteps := 500)
@[fun_prop] theorem unpack_comp (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => unpack (Γ:=Γ) (Q:=Q) (f x) (g x)) := by unfold unpack; fun_prop (maxSteps := 500)

@[fun_prop] theorem encodeNum_comp (z : Γ) (f : α → ℕ) (g : α → StateRep Γ)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun x => encodeNum (Q:=Q) z (f x) (g x)) := by
  unfold encodeNum
  fun_prop (maxSteps := 500)
@[fun_prop] theorem decodeNum_comp (z : Γ) (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => decodeNum (Γ:=Γ) (Q:=Q) z (f x) (g x)) := by unfold decodeNum; fun_prop (maxSteps := 500)

@[simp] theorem label_default (e : ℕ) : (labelCoding (Coding.fixed Q) e).enc default=0 := rfl

@[fun_prop] theorem boolOr_comp (f g : α → Bool) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun x => (f x)||(g x)) := Primrec.or.comp hf hg

@[fun_prop] theorem localNum_comp (M : TM0.Machine Γ Q) (a z sep : Γ)
    (e : α → ℕ) (l c r : α → CellRep Γ)
    (he : Primrec e) (hl : Primrec l) (hc : Primrec c) (hr : Primrec r) :
    Primrec (fun x => localNum M a z sep (e x) (l x) (c x) (r x)) := by
  unfold localNum
  fun_prop (maxSteps := 500)
@[fun_prop] theorem halfNum_comp (M : TM0.Machine Γ Q) (a z sep : Γ)
    (e : α → ℕ) (l : α → Option (CellRep Γ × CellRep Γ)) (c r : α → CellRep Γ × CellRep Γ)
    (he : Primrec e) (hl : Primrec l) (hc : Primrec c) (hr : Primrec r) :
    Primrec (fun x => SimulatorFold.halfRule (localNum M a z sep (e x)) (l x) (c x) (r x)) := by
  unfold SimulatorFold.halfRule
  fun_prop (maxSteps := 500)
@[fun_prop] theorem trackNum_comp (M : TM0.Machine Γ Q) (a z sep : Γ)
    (e : α → ℕ) (l : α → Option (TrackRep Γ)) (c r : α → TrackRep Γ) (b : α → Bool)
    (he : Primrec e) (hl : Primrec l) (hc : Primrec c) (hr : Primrec r) (hb : Primrec b) :
    Primrec (fun x => trackNum M a z sep (e x) (l x) (c x) (r x) (b x)) := by
  unfold trackNum
  fun_prop (maxSteps := 500)
@[fun_prop] theorem alarmNum_comp (M : TM0.Machine Γ Q) (a z sep : Γ)
    (e : α → ℕ) (c : α → TrackRep Γ) (he : Primrec e) (hc : Primrec c) :
    Primrec (fun x => alarmNum M a z sep (e x) (c x)) := by
  unfold alarmNum
  fun_prop (maxSteps := 500)
@[fun_prop] theorem monitoredNum_comp (M : TM0.Machine Γ Q) (a z sep : Γ)
    (e : α → ℕ) (l : α → Option (TrackRep Γ)) (c r : α → TrackRep Γ) (b : α → Bool)
    (he : Primrec e) (hl : Primrec l) (hc : Primrec c) (hr : Primrec r) (hb : Primrec b) :
    Primrec (fun x => monitoredNum M a z sep (e x) (l x) (c x) (r x) (b x)) := by
  unfold monitoredNum
  fun_prop (maxSteps := 500)

@[fun_prop] theorem updateNum_comp (M : TM0.Machine Γ Q) (a z sep : Γ)
    (e : α → ℕ) (l : α → Option (StateRep Γ)) (c r : α → StateRep Γ) (b : α → Bool)
    (he : Primrec e) (hl : Primrec l) (hc : Primrec c) (hr : Primrec r) (hb : Primrec b) :
    Primrec (fun x => updateNum M a z sep (e x) (l x) (c x) (r x) (b x)) := by
  unfold updateNum
  simp only [label_default]
  fun_prop (maxSteps := 500)

@[fun_prop] theorem stateSize_comp (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun x => (stateCoding (Coding.fixed Γ) (Coding.fixed Q) (f x)).size) := by
  unfold stateCoding Coding.prod Coding.option labelCoding
  dsimp only
  fun_prop (maxSteps := 500)

variable (M : TM0.Machine Γ Q) (a z sep : Γ)
theorem entryNum_primrec : Primrec (fun p : ℕ × ℕ => entryNum M a z sep p.1 p.2) := by
  let n : ℕ × ℕ → ℕ := fun p => (stateCoding (Coding.fixed Γ) (Coding.fixed Q) p.1).size+3
  let q : ℕ × ℕ → ℕ := fun p => p.2/2/n p/n p
  let l : ℕ × ℕ → Option ℕ := fun p => if q p=0 then none else some ((q p-1)%n p)
  let c : ℕ × ℕ → ℕ := fun p => (p.2/2/n p)%n p
  let r : ℕ × ℕ → ℕ := fun p => (p.2/2)%n p
  let b : ℕ × ℕ → Bool := fun p => decide (p.2%2=1)
  have hn : Primrec n := Primrec.nat_add.comp
    (stateSize_comp (Γ:=Γ) (Q:=Q) (fun p : ℕ × ℕ => p.1) Primrec.fst) (Primrec.const 3)
  have hu : Primrec (fun p : ℕ × ℕ => p.2/2) := Primrec.nat_div.comp Primrec.snd (Primrec.const 2)
  have hq : Primrec q := Primrec.nat_div.comp (Primrec.nat_div.comp hu hn) hn
  have hl : Primrec l := Primrec.ite (Primrec.eq.comp hq (Primrec.const 0)) (Primrec.const none)
    (Primrec.option_some.comp (Primrec.nat_mod.comp (Primrec.nat_sub.comp hq (Primrec.const 1)) hn))
  have hc : Primrec c := Primrec.nat_mod.comp (Primrec.nat_div.comp hu hn) hn
  have hr : Primrec r := Primrec.nat_mod.comp hu hn
  have hb : Primrec b := (Primrec.eq.comp
    (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1)).decide
  have hg : Primrec (fun p : (ℕ × ℕ) × ℕ => decodeNum (Γ:=Γ) (Q:=Q) z p.1.1 p.2) := by
    fun_prop (maxSteps := 500)
  have hlmap : Primrec (fun p : ℕ × ℕ => (l p).map (fun k => decodeNum (Γ:=Γ) (Q:=Q) z p.1 k)) :=
    Primrec.option_map hl hg.to₂
  have hdc := decodeNum_comp (Γ:=Γ) (Q:=Q) z (fun p : ℕ × ℕ => p.1) c Primrec.fst hc
  have hdr := decodeNum_comp (Γ:=Γ) (Q:=Q) z (fun p : ℕ × ℕ => p.1) r Primrec.fst hr
  have hup := updateNum_comp M a z sep (fun p : ℕ × ℕ => p.1)
    (fun p => (l p).map (fun k => decodeNum (Γ:=Γ) (Q:=Q) z p.1 k))
    (fun p => decodeNum (Γ:=Γ) (Q:=Q) z p.1 (c p))
    (fun p => decodeNum (Γ:=Γ) (Q:=Q) z p.1 (r p)) b Primrec.fst hlmap hdc hdr hb
  have hout := encodeNum_comp (Q:=Q) z (fun p : ℕ × ℕ => p.1) _ Primrec.fst hup
  have hguard : PrimrecPred (fun p => l p=some 1 ∧ c p=1 ∧ r p=1) :=
    (Primrec.eq.comp hl (Primrec.const (some 1))).and
      ((Primrec.eq.comp hc (Primrec.const 1)).and (Primrec.eq.comp hr (Primrec.const 1)))
  have hh := Primrec.ite hguard (Primrec.const 1) hout
  exact hh.of_eq (fun p => rfl)

theorem localEntry_primrec : Primrec₂ (fun e k => SimulatorEncoding.localEntry
    (family M a z sep (Coding.fixed Γ) (Coding.fixed Q) e) k) :=
  (entryNum_primrec M a z sep).of_eq fun p => (entry_eq M a z sep p.1 p.2).symm

#print axioms localEntry_primrec
end Sigma2.SimulatorEffectiveKernel

