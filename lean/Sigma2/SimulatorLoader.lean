import Sigma2.SimulatorReject

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorLoader
open Turing Sigma2.Tree Sigma2.SimulatorLocal Sigma2.SimulatorFold

inductive Control | origin | scan | back
  deriving DecidableEq, Fintype

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]
abbrev State (Γ Q : Type) := Option Control × SimulatorTracks.State Γ Q

def headless (k : Option Control) (f : Fin 5) (a : Γ) : State Γ Q :=
  (k, (f, ((a, none), (default, none))))

def command (l : Option (Option Control)) (c r : Option Control) (b : Bool) :
    Option Control × Bool × Bool :=
  if l=some (some .origin) then (some .scan, true, false) else
  if l=some (some .scan) then
    if b then (some .back, false, false) else (some .scan, true, false) else
  if r=some .back then (some .back, false, false) else
  if c=some .back ∧ l=none then (none, false, true) else (none, false, false)

def update (M : TM0.Machine Γ Q) (a : Γ) (l : Option (State Γ Q))
    (c r : State Γ Q) (b : Bool) : State Γ Q :=
  let d := command (l.map Prod.fst) c.1 r.1 b
  let s := SimulatorReject.monitoredUpdate M (l.map Prod.snd) c.2 r.2 b
  (d.1, (s.1, (if d.2.1 then (a, none) else
    if d.2.2 then (s.2.1.1, some default) else s.2.1, s.2.2)))

def rule (M : TM0.Machine Γ Q) (a z : Γ) : SimulatorAlphabet.Rule (State Γ Q) where
  start := headless (some .origin) 0 z
  blank := headless none 1 default
  reject := (none, SimulatorTracks.reject)
  start_ne_blank := by intro h; have := congrArg Prod.fst h; simp [headless] at this
  start_ne_reject := by intro h; have := congrArg Prod.fst h; simp [headless] at this
  blank_ne_reject := by intro h; have := congrArg (fun c => c.2.1) h; simp [headless, SimulatorTracks.reject] at this
  update := update M a
  quiescence := by
    intro b
    simp [update, command, headless, SimulatorReject.monitoredUpdate,
      SimulatorReject.alarm, SimulatorReject.cellHalted, SimulatorTracks.update,
      SimulatorTracks.blank, SimulatorTracks.vacant, halfRule, localRule,
      written, stationary, incoming]

/-- The data track written by a front that has reached t. -/
def unaryTape (a z : Γ) (t x : ℕ) : Γ :=
  if x=0 then z else if x≤t then a else default

def outward (a z : Γ) (pulse : ℕ → Bool) (t x : ℕ) : State Γ Q :=
  headless (if x=t then some (if t=0 then .origin else .scan) else none)
    (run SimulatorFront.front pulse t x) (unaryTape a z t x)

def returning (a z : Γ) (pulse : ℕ → Bool) (q t p x : ℕ) : State Γ Q :=
  headless (if x=p then some .back else none)
    (run SimulatorFront.front pulse t x) (unaryTape a z q x)

lemma update_headless (M : TM0.Machine Γ Q) (a : Γ)
    (l : Option (Option Control × Fin 5 × Γ))
    (k j : Option Control) (f g : Fin 5) (u v : Γ) (b : Bool)
    (hf : f≠2) :
    update M a (l.map (fun s => headless s.1 s.2.1 s.2.2))
      (headless k f u) (headless j g v) b =
    let d := command (l.map Prod.fst) k j b
    (d.1, (SimulatorFront.front.update (l.map (fun s => s.2.1)) f g b,
      ((if d.2.1 then a else u, if d.2.1 then none else if d.2.2 then some default else none),
        (default, none)))) := by
  cases l <;>
    simp [update, headless, SimulatorReject.monitoredUpdate, SimulatorReject.alarm,
      SimulatorReject.cellHalted, SimulatorTracks.update, halfRule, localRule,
      written, stationary, incoming, hf]
  all_goals split_ifs <;> rfl


def field (ctl : ℕ → Option Control) (data : ℕ → Γ) (pulse : ℕ → Bool)
    (t x : ℕ) : State Γ Q := headless (ctl x) (run SimulatorFront.front pulse t x) (data x)

lemma field_step (M : TM0.Machine Γ Q) (a : Γ) (ctl : ℕ → Option Control)
    (data : ℕ → Γ) (pulse : ℕ → Bool) (t x : ℕ) :
    update M a (if x=0 then none else some (field ctl data pulse t (x-1)))
      (field ctl data pulse t x) (field ctl data pulse t (x+1)) (pulse t) =
    let d := command (if x=0 then none else some (ctl (x-1))) (ctl x) (ctl (x+1)) (pulse t)
    (d.1, (run SimulatorFront.front pulse (t+1) x,
      ((if d.2.1 then a else data x,
        if d.2.1 then none else if d.2.2 then some default else none), (default, none)))) := by
  have h := update_headless M a
    (if x=0 then none else some (ctl (x-1),
      run SimulatorFront.front pulse t (x-1), data (x-1)))
    (ctl x) (ctl (x+1)) (run SimulatorFront.front pulse t x)
    (run SimulatorFront.front pulse t (x+1)) (data x) (data (x+1)) (pulse t)
    (SimulatorReject.front_ne_two pulse t x)
  by_cases hx : x=0 <;> simpa only [hx, if_true, if_false, Option.map_none,
    Option.map_some, field, run] using h

def outwardControl (t x : ℕ) : Option Control :=
  if x=t then some (if t=0 then .origin else .scan) else none

lemma outwardControl_ne_back (t x : ℕ) : outwardControl t x ≠ some .back := by
  unfold outwardControl
  split_ifs <;> decide

lemma outward_command (pulse : ℕ → Bool) (t : ℕ) (ht : t=0 ∨ pulse t=false) (x : ℕ) :
    command (if x=0 then none else some (outwardControl t (x-1)))
      (outwardControl t x) (outwardControl t (x+1)) (pulse t) =
      (if x=t+1 then some .scan else none, decide (x=t+1), false) := by
  by_cases hn : x=t+1
  · subst x
    cases t with
    | zero => simp [command, outwardControl]
    | succ t =>
      have hb : pulse (t+1)=false := ht.resolve_left (by omega)
      simp [command, outwardControl, hb]
  · have hl : (if x=0 then none else some (outwardControl t (x-1))) = (if x=0 then none else some none) := by
      by_cases hx : x=0
      · simp [hx]
      · simp [hx, outwardControl, show x-1≠t by omega]
    rw [hl]
    by_cases hx : x=0 <;> simp [command, hx, hn, outwardControl_ne_back]

lemma unaryTape_step (a z : Γ) (t x : ℕ) :
    (if x=t+1 then a else unaryTape a z t x) = unaryTape a z (t+1) x := by
  unfold unaryTape
  split_ifs <;> simp_all <;> omega

/-- A standard-seed unary front ignores the origin pulse. -/
theorem outward_step (M : TM0.Machine Γ Q) (a z : Γ) (pulse : ℕ → Bool)
    (t : ℕ) (ht : t=0 ∨ pulse t=false) (x : ℕ) :
    update M a (if x=0 then none else some (outward a z pulse t (x-1)))
      (outward a z pulse t x) (outward a z pulse t (x+1)) (pulse t) =
        outward a z pulse (t+1) x := by
  change update M a (if x=0 then none else some
    (field (outwardControl t) (unaryTape a z t) pulse t (x-1)))
    (field (outwardControl t) (unaryTape a z t) pulse t x)
    (field (outwardControl t) (unaryTape a z t) pulse t (x+1)) (pulse t) = _
  rw [field_step, outward_command pulse t ht x]
  simp only [decide_eq_true_eq, Bool.false_eq_true, ite_false, ite_self]
  change ((if x=t+1 then some Control.scan else none, (run SimulatorFront.front pulse (t+1) x,
    ((if x=t+1 then a else unaryTape a z t x, none), (default, none)))) : State Γ Q) = _
  rw [unaryTape_step]
  simp [outward, headless]

theorem typed_outward (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q) :
    ∀ t, t≤q → ∀ x,
      SimulatorAlphabet.typedRun (rule M a z) (fun s => decide (q ∣ s)) t x =
        outward a z (fun s => decide (q ∣ s)) t x := by
  intro t
  induction t with
  | zero =>
    intro _ x
    by_cases hx : x=0 <;>
      simp [SimulatorAlphabet.typedRun, rule, outward, headless, unaryTape, run, hx]
  | succ t ih =>
    intro ht x
    change update M a (if x=0 then none else some
      (SimulatorAlphabet.typedRun (rule M a z) (fun s => decide (q ∣ s)) t (x-1)))
      (SimulatorAlphabet.typedRun (rule M a z) (fun s => decide (q ∣ s)) t x)
      (SimulatorAlphabet.typedRun (rule M a z) (fun s => decide (q ∣ s)) t (x+1))
      (decide (q ∣ t)) = _
    simp only [ih (by omega)]
    apply outward_step
    by_cases hz : t=0
    · exact Or.inl hz
    · exact Or.inr (by simp [Nat.not_dvd_of_pos_of_lt (by omega : 0<t) (by omega : t<q)])

lemma stop_command (q : ℕ) (hq : 0<q) (x : ℕ) :
    command (if x=0 then none else some (outwardControl q (x-1)))
      (outwardControl q x) (outwardControl q (x+1)) true =
        (if x=q+1 then some .back else none, false, false) := by
  by_cases hn : x=q+1
  · subst x; simp [command, outwardControl, show q≠0 by omega]
  · have hl : (if x=0 then none else some (outwardControl q (x-1))) = (if x=0 then none else some none) := by
      by_cases hx : x=0
      · simp [hx]
      · simp [hx, outwardControl, show x-1≠q by omega]
    rw [hl]
    by_cases hx : x=0 <;> simp [command, hx, hn, outwardControl_ne_back]

theorem stop_step (M : TM0.Machine Γ Q) (a z : Γ) (pulse : ℕ → Bool)
    (q : ℕ) (hq : 0<q) (hb : pulse q=true) (x : ℕ) :
    update M a (if x=0 then none else some (outward a z pulse q (x-1)))
      (outward a z pulse q x) (outward a z pulse q (x+1)) (pulse q) =
        returning a z pulse q (q+1) (q+1) x := by
  change update M a (if x=0 then none else some
    (field (outwardControl q) (unaryTape a z q) pulse q (x-1)))
    (field (outwardControl q) (unaryTape a z q) pulse q x)
    (field (outwardControl q) (unaryTape a z q) pulse q (x+1)) (pulse q) = _
  rw [field_step, hb, stop_command q hq x]
  rfl

lemma return_command (p : ℕ) (hp : 0<p) (x : ℕ) (b : Bool) :
    command (if x=0 then none else some (if x-1=p then some .back else none))
      (if x=p then some .back else none) (if x+1=p then some .back else none) b =
        (if x=p-1 then some .back else none, false, false) := by
  unfold command
  by_cases hx : x=0 <;> by_cases hc : x=p <;> by_cases hl : x-1=p <;>
    by_cases hr : x+1=p <;> by_cases hn : x=p-1 <;>
      simp_all <;> omega

theorem return_step (M : TM0.Machine Γ Q) (a z : Γ) (pulse : ℕ → Bool)
    (q t p : ℕ) (hp : 0<p) (x : ℕ) :
    update M a (if x=0 then none else some (returning a z pulse q t p (x-1)))
      (returning a z pulse q t p x) (returning a z pulse q t p (x+1)) (pulse t) =
        returning a z pulse q (t+1) (p-1) x := by
  change update M a (if x=0 then none else some
    (field (fun y => if y=p then some .back else none) (unaryTape a z q) pulse t (x-1)))
    (field (fun y => if y=p then some .back else none) (unaryTape a z q) pulse t x)
    (field (fun y => if y=p then some .back else none) (unaryTape a z q) pulse t (x+1))
    (pulse t) = _
  rw [field_step, return_command p hp x (pulse t)]
  rfl

theorem typed_returning (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q) :
    ∀ j, j≤q+1 → ∀ x,
      SimulatorAlphabet.typedRun (rule M a z) (fun s => decide (q ∣ s)) (q+1+j) x =
        returning a z (fun s => decide (q ∣ s)) q (q+1+j) (q+1-j) x := by
  intro j
  induction j with
  | zero =>
    intro _ x
    change update M a _ _ _ _ = _
    simp only [typed_outward M a z q hq q le_rfl]
    simpa using stop_step M a z (fun s => decide (q ∣ s)) q hq (by simp) x
  | succ j ih =>
    intro hj x
    have ht : q+1+(j+1) = (q+1+j)+1 := by omega
    rw [ht]
    change update M a _ _ _ _ = _
    simp only [ih (by omega)]
    simpa only [show q+1-j-1=q+1-(j+1) by omega] using
      return_step M a z (fun s => decide (q ∣ s)) q (q+1+j) (q+1-j) (by omega) x

lemma launch_command (x : ℕ) (b : Bool) :
    command (if x=0 then none else some (if x-1=0 then some .back else none))
      (if x=0 then some .back else none) (if x+1=0 then some .back else none) b =
        (none, false, decide (x=0)) := by
  by_cases hx : x=0 <;> by_cases hl : x-1=0 <;> simp [command, hx, hl]

lemma initial_unary_picture (a z : Γ) (q x : ℕ) :
    fold (picture (0, (TM0.init (z :: List.replicate q a) : TM0.Cfg Γ Q))) x =
      ((unaryTape a z q x, if x=0 then some default else none), (default, none)) := by
  have hpos (x : ℕ) : (Tape.mk₁ (z :: List.replicate q a)).nth (x : ℤ) =
      unaryTape a z q x := by
    simp only [Tape.mk₁, Tape.mk₂, Tape.mk'_nth_nat, ListBlank.nth_mk]
    cases x with
    | zero => simp [unaryTape]
    | succ x =>
      rw [List.getI_cons_succ]
      by_cases hx : x<q
      · rw [List.getI_eq_getElem _ (by simpa using hx), List.getElem_replicate]
        simp [unaryTape, show x+1≠0 by omega, show x+1≤q by omega]
      · rw [List.getI_eq_default _ (by simpa using Nat.le_of_not_gt hx)]
        simp [unaryTape, show x+1≠0 by omega, show ¬x+1≤q by omega]
  have hneg : (Tape.mk₁ (z :: List.replicate q a)).nth (-(x : ℤ)-1) = default := by
    rw [show -(x : ℤ)-1 = Int.negSucc x by omega]
    simp [Tape.mk₁, Tape.mk₂, Tape.mk', Tape.nth]
  have hn : -(x : ℤ)-1 ≠ 0 := by omega
  dsimp only [fold, picture, TM0.init]
  simp only [sub_zero, hpos, hneg, if_neg hn]
  by_cases hx : x=0 <;> simp [hx]

def runningSnapshot (M : TM0.Machine Γ Q) (a z : Γ) (pulse : ℕ → Bool)
    (q T s x : ℕ) : State Γ Q :=
  (none, (run SimulatorFront.front pulse (T+s) x,
    fold (picture ((advance M)^[s] (0, TM0.init (z :: List.replicate q a)))) x))

/-- At the exact release time the standard seed has become a prepared tape,
with one head at the checked simulator entry and no remaining loader control. -/
theorem typed_handoff (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q) (x : ℕ) :
    SimulatorAlphabet.typedRun (rule M a z) (fun s => decide (q ∣ s)) (2*q+3) x =
      runningSnapshot M a z (fun s => decide (q ∣ s)) q (2*q+3) 0 x := by
  have he : 2*q+3 = (q+1+(q+1))+1 := by omega
  rw [he]
  change update M a _ _ _ _ = _
  simp only [typed_returning M a z q hq (q+1) le_rfl, Nat.sub_self]
  change update M a (if x=0 then none else some
    (field (fun y => if y=0 then some .back else none) (unaryTape a z q)
      (fun s => decide (q ∣ s)) (q+1+(q+1)) (x-1)))
    (field (fun y => if y=0 then some .back else none) (unaryTape a z q)
      (fun s => decide (q ∣ s)) (q+1+(q+1)) x)
    (field (fun y => if y=0 then some .back else none) (unaryTape a z q)
      (fun s => decide (q ∣ s)) (q+1+(q+1)) (x+1)) _ = _
  rw [field_step, launch_command]
  simp only [runningSnapshot, Function.iterate_zero_apply, Nat.add_zero, initial_unary_picture,
    Bool.false_eq_true, Bool.decide_coe, decide_eq_true_eq, ite_false]

lemma update_running (M : TM0.Machine Γ Q) (a : Γ)
    (l : Option (SimulatorTracks.State Γ Q)) (c r : SimulatorTracks.State Γ Q) (b : Bool) :
    update M a (l.map (fun s => (none,s))) (none,c) (none,r) b =
      (none, SimulatorReject.monitoredUpdate M l c r b) := by
  cases l <;> simp [update, command]

lemma runningSnapshot_step (M : TM0.Machine Γ Q) (a z : Γ) (pulse : ℕ → Bool)
    (q T s x : ℕ)
    (hc : TM0.step M ((advance M)^[s] (0, TM0.init (z :: List.replicate q a))).2 ≠ none) :
    update M a (if x=0 then none else some (runningSnapshot M a z pulse q T s (x-1)))
      (runningSnapshot M a z pulse q T s x) (runningSnapshot M a z pulse q T s (x+1))
      (pulse (T+s)) = runningSnapshot M a z pulse q T (s+1) x := by
  have hu := update_running M a
    (if x=0 then none else some (runningSnapshot M a z pulse q T s (x-1)).2)
    (runningSnapshot M a z pulse q T s x).2
    (runningSnapshot M a z pulse q T s (x+1)).2 (pulse (T+s))
  simp only [apply_ite, Option.map_none, Option.map_some] at hu
  simp only [runningSnapshot] at hu ⊢
  rw [hu]
  have ha := SimulatorReject.alarm_false M
    ((advance M)^[s] (0, TM0.init (z :: List.replicate q a)))
    (run SimulatorFront.front pulse (T+s) x) x hc
  have hf := SimulatorReject.front_ne_two pulse (T+s) x
  simp only [SimulatorReject.monitoredUpdate, runningSnapshot, hf, ha, Bool.false_eq_true,
    or_self, ite_false]
  congr 1
  apply Prod.ext
  · simp [SimulatorTracks.update, run, Nat.add_assoc]
  · have hh := congrFun (halfStep_picture M
      ((advance M)^[s] (0, TM0.init (z :: List.replicate q a)))) x
    by_cases hx : x=0 <;>
      simpa [SimulatorTracks.update, halfStep, hx, Function.iterate_succ_apply'] using hh

/-- The checked folded simulator now runs in the actual standard-seed run. -/
theorem safe_simulation (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q) :
    ∀ s, (∀ j<s, TM0.step M ((advance M)^[j]
      (0, TM0.init (z :: List.replicate q a))).2 ≠ none) → ∀ x,
      SimulatorAlphabet.typedRun (rule M a z) (fun t => decide (q ∣ t)) (2*q+3+s) x =
        runningSnapshot M a z (fun t => decide (q ∣ t)) q (2*q+3) s x := by
  intro s
  induction s with
  | zero => intro _ x; exact typed_handoff M a z q hq x
  | succ s ih =>
    intro hs x
    have ht : 2*q+3+(s+1) = (2*q+3+s)+1 := by omega
    rw [ht]
    change update M a _ _ _ _ = _
    simp only [ih (fun j hj => hs j (by omega))]
    exact runningSnapshot_step M a z _ q (2*q+3) s x (hs s (by omega))

theorem typed_loading_safe (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q)
    (t x : ℕ) (ht : t<2*q+3) :
    SimulatorAlphabet.typedRun (rule M a z) (fun s => decide (q ∣ s)) t x ≠
      (rule M a z).reject := by
  intro h
  by_cases htq : t≤q
  · rw [typed_outward M a z q hq t htq] at h
    have hf := congrArg (fun s : State Γ Q => s.2.1) h
    exact SimulatorReject.front_ne_two _ t x hf
  · have hj : t-(q+1)≤q+1 := by omega
    have he : t=q+1+(t-(q+1)) := by omega
    rw [he, typed_returning M a z q hq _ hj] at h
    have hf := congrArg (fun s : State Γ Q => s.2.1) h
    exact SimulatorReject.front_ne_two _ _ x hf

variable [Fintype Γ] [Fintype Q] [DecidableEq Γ] [DecidableEq Q]

def automaton (M : TM0.Machine Γ Q) (a z : Γ) : Automaton :=
  SimulatorAlphabet.automaton (rule M a z)

lemma run_encode {A : Type} [Fintype A] [DecidableEq A] (D : SimulatorAlphabet.Rule A)
    (pulse : ℕ → Bool) (t x : ℕ) :
    SimulatorAlphabet.encode D (SimulatorAlphabet.typedRun D pulse t x) =
      run (SimulatorAlphabet.automaton D) pulse t x := by
  rw [← SimulatorAlphabet.decode_run]
  cases t with
  | zero => by_cases hx : x=0 <;> simp [run, hx]
  | succ t =>
    simp only [run, SimulatorAlphabet.automaton]
    split_ifs <;> simp_all

/-- No rejection anywhere through q, in Tree.run itself and independently of
all verifier runtime behavior. The stronger bound covers the whole loader. -/
theorem initial_safe (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q)
    (t x : ℕ) (ht : t<2*q+3) :
    run (automaton M a z) (fun s => decide (q ∣ s)) t x ≠ 2 := by
  intro h
  have he := SimulatorAlphabet.decode_run (rule M a z) (fun s => decide (q ∣ s)) t x
  change SimulatorAlphabet.decode (rule M a z) (run (automaton M a z) _ t x) = _ at he
  rw [h, SimulatorAlphabet.decode_two] at he
  exact typed_loading_safe M a z q hq t x ht he.symm

/-- The actual standard-seed computation retains the frozen pulse cells
throughout loading, including the return trip. -/
theorem front_while_loading (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q)
    (t x : ℕ) (ht : t<2*q+3) :
    (SimulatorAlphabet.decode (rule M a z)
      (run (automaton M a z) (fun s => decide (q ∣ s)) t x)).2.1 =
        run SimulatorFront.front (fun s => decide (q ∣ s)) t x := by
  change (SimulatorAlphabet.decode (rule M a z)
    (run (SimulatorAlphabet.automaton (rule M a z)) (fun s => decide (q ∣ s)) t x)).2.1 = _
  rw [SimulatorAlphabet.decode_run]
  by_cases htq : t≤q
  · rw [typed_outward M a z q hq t htq]
    rfl
  · have hj : t-(q+1)≤q+1 := by omega
    have he : t=q+1+(t-(q+1)) := by omega
    rw [he, typed_returning M a z q hq _ hj]
    rfl

theorem frozen_period_loading (M : TM0.Machine Γ Q) (a z : Γ) (q : ℕ) (hq : 0<q)
    (t : ℕ) (htq : q+1≤t) (ht : t<2*q+3) :
    (SimulatorAlphabet.decode (rule M a z)
      (run (automaton M a z) (fun s => decide (q ∣ s)) t 1)).2.1=4 ∧
    (∀ x, 1<x → x≤q → (SimulatorAlphabet.decode (rule M a z)
      (run (automaton M a z) (fun s => decide (q ∣ s)) t x)).2.1=3) ∧
    (SimulatorAlphabet.decode (rule M a z)
      (run (automaton M a z) (fun s => decide (q ∣ s)) t (q+1))).2.1=4 := by
  simpa only [front_while_loading M a z q hq t _ ht] using
    SimulatorFront.front_period_input q hq t htq

#print axioms frozen_period_loading

#print axioms typed_outward
#print axioms typed_returning
#print axioms typed_handoff
#print axioms safe_simulation
#print axioms initial_safe
end Sigma2.SimulatorLoader
