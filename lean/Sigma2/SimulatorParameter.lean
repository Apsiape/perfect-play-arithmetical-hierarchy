import Sigma2.SimulatorPair

noncomputable section
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
namespace Sigma2.SimulatorParameter
open Turing Relation

inductive Label (e : ℕ) (Q : Type)
  | scan | sepMove | fill (i : Fin (e+1)) | right (i : Fin (e+1)) | back | run (q : Q)
  deriving DecidableEq, Fintype

instance {e : ℕ} {Q : Type} : Inhabited (Label e Q) := ⟨.scan⟩

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q] [DecidableEq Γ]

/-- Scan the loaded q block, append a separator and e unary cells, return to
its bottom mark, and enter the one fixed verifier. -/
def machine (M : TM0.Machine Γ Q) (a z sep : Γ) (e : ℕ) : TM0.Machine Γ (Label e Q)
  | .scan, s => if s=default then some (.sepMove, .write sep)
      else some (.scan, .move .right)
  | .sepMove, _ => some (.fill ⟨e, by omega⟩, .move .right)
  | .fill i, s => if h : i.val=0 then some (.back, .write s)
      else some (.right ⟨i.val-1, by omega⟩, .write a)
  | .right i, _ => some (.fill i, .move .right)
  | .back, s => if s=z then some (.run default, .write s)
      else some (.back, .move .left)
  | .run q, s => (M q s).map (fun p => (.run p.1, p.2))

variable (M : TM0.Machine Γ Q) (a z sep : Γ) (e : ℕ)

lemma move_right (L R : List Γ) (h : Γ) :
    (Tape.mk₂ L (h::R)).move .right = Tape.mk₂ (h::L) R := by
  simp [Tape.mk₂, Tape.move_right_mk']

lemma move_left (L R : List Γ) (h : Γ) :
    (Tape.mk₂ (h::L) R).move .left = Tape.mk₂ L (h::R) := by
  simp [Tape.mk₂, Tape.move_left_mk']

lemma write_empty (L : List Γ) (s : Γ) :
    (Tape.mk₂ L []).write s = Tape.mk₂ L [s] := by
  simp [Tape.mk₂, Tape.write_mk']

lemma single {c d : TM0.Cfg Γ (Label e Q)}
    (h : TM0.step (machine M a z sep e) c = some d) :
    TM0.Reaches (machine M a z sep e) c d := ReflTransGen.single h

/-- The initial scan terminates exactly at the first blank. -/
lemma scan_reaches (L v : List Γ) (hv : ∀ s∈v, s≠default) :
    TM0.Reaches (machine M a z sep e)
      ⟨.scan, Tape.mk₂ L v⟩
      ⟨.sepMove, Tape.mk₂ (v.reverse ++ L) [sep]⟩ := by
  induction v generalizing L with
  | nil =>
    apply single
    simp [TM0.step, machine, Tape.mk₂, Tape.mk', Tape.write, ListBlank.head_mk]
  | cons s v ih =>
    have hs : s≠default := hv s (by simp)
    have hstep : TM0.Reaches (machine M a z sep e)
        ⟨.scan, Tape.mk₂ L (s::v)⟩ ⟨.scan, Tape.mk₂ (s::L) v⟩ := by
      apply single
      simp [TM0.step, machine, Tape.mk₂, Tape.mk', hs, Tape.move]
    have hh := hstep.trans (ih (s::L) (fun t ht => hv t (by simp [ht])))
    simpa [TM0.Reaches, List.reverse_cons, List.append_assoc] using hh

/-- The counter is a finite, explicit descending chain. -/
lemma fill_reaches (i : ℕ) (hi : i<e+1) (L : List Γ) :
    TM0.Reaches (machine M a z sep e)
      ⟨.fill ⟨i,hi⟩, Tape.mk₂ L []⟩
      ⟨.fill ⟨0,by omega⟩, Tape.mk₂ (List.replicate i a ++ L) []⟩ := by
  induction i generalizing L with
  | zero => exact ReflTransGen.refl
  | succ i ih =>
    have h1 : TM0.Reaches (machine M a z sep e)
        ⟨.fill ⟨i+1,hi⟩, Tape.mk₂ L []⟩
        ⟨.right ⟨i,by omega⟩, Tape.mk₂ L [a]⟩ := by
      apply single
      simp [TM0.step, machine, write_empty]
    have h2 : TM0.Reaches (machine M a z sep e)
        ⟨.right ⟨i,by omega⟩, Tape.mk₂ L [a]⟩
        ⟨.fill ⟨i,by omega⟩, Tape.mk₂ (a::L) []⟩ := by
      apply single
      simp [TM0.step, machine, move_right]
    have hh := (h1.trans h2).trans (ih (by omega) (a::L))
    simpa [TM0.Reaches, List.replicate_succ', List.append_assoc] using hh

/-- Return through an arbitrary word containing no bottom mark. -/
lemma back_reaches (v : List Γ) (s : Γ) (R : List Γ)
    (hs : s≠z) (hv : ∀ t∈v, t≠z) :
    TM0.Reaches (machine M a z sep e)
      ⟨.back, Tape.mk₂ (v ++ [z]) (s::R)⟩
      ⟨.run default, Tape.mk₁ (z :: (v.reverse ++ s::R))⟩ := by
  have step : TM0.Reaches (machine M a z sep e)
      ⟨.back, Tape.mk₂ (v ++ [z]) (s::R)⟩
      ⟨.back, (Tape.mk₂ (v ++ [z]) (s::R)).move .left⟩ := by
    apply single
    simp [TM0.step, machine, Tape.mk₂, Tape.mk', hs]
  induction v generalizing s R with
  | nil =>
    have hend : TM0.Reaches (machine M a z sep e)
        ⟨.back, Tape.mk₂ [] (z::s::R)⟩
        ⟨.run default, Tape.mk₁ (z::s::R)⟩ := by
      apply single
      simp [TM0.step, machine, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.write]
    simpa [TM0.Reaches, move_left] using step.trans hend
  | cons t v ih =>
    have hnext := ih t (s::R) (hv t (by simp)) (fun u hu => hv u (by simp [hu])) (by
      apply single
      simp [TM0.step, machine, Tape.mk₂, Tape.mk', hv t (by simp)])
    have hh := step.trans (by simpa [TM0.Reaches, move_left] using hnext)
    simpa [TM0.Reaches, List.reverse_cons, List.append_assoc] using hh

@[simp] lemma trailing_blank (L v : List Γ) :
    Tape.mk₂ L (v ++ [default]) = Tape.mk₂ L v := by
  apply congrArg (Tape.mk' (ListBlank.mk L))
  exact Quotient.sound' (Or.inr ⟨1, by simp⟩)

/-- The explicit initialization chain reaches the fixed verifier on the pair tape. -/
theorem handoff (q : ℕ) (ha : a≠default) (hz : z≠default)
    (haz : a≠z) (hsep : sep≠z) :
    TM0.Reaches (machine M a z sep e)
      (TM0.init (z :: List.replicate q a))
      ⟨.run default, Tape.mk₁ (z :: (List.replicate q a ++
        sep :: List.replicate e a))⟩ := by
  have hscan := scan_reaches M a z sep e [] (z :: List.replicate q a) (by
    intro s hs
    simp only [List.mem_cons, List.mem_replicate] at hs
    rcases hs with rfl | ⟨_,rfl⟩
    · exact hz
    · exact ha)
  have hmove : TM0.Reaches (machine M a z sep e)
      ⟨.sepMove, Tape.mk₂ (List.replicate q a ++ [z]) [sep]⟩
      ⟨.fill ⟨e,by omega⟩, Tape.mk₂ (sep :: (List.replicate q a ++ [z])) []⟩ := by
    apply single
    simp [TM0.step, machine, move_right]
  have hfill := fill_reaches M a z sep e e (by omega)
    (sep :: (List.replicate q a ++ [z]))
  let v := List.replicate e a ++ sep :: List.replicate q a
  have hzero : TM0.Reaches (machine M a z sep e)
      ⟨.fill ⟨0,by omega⟩, Tape.mk₂ (v ++ [z]) []⟩
      ⟨.back, Tape.mk₂ (v ++ [z]) [default]⟩ := by
    apply single
    simp [TM0.step, machine, write_empty, Tape.mk₂, Tape.mk']
  have hback := back_reaches M a z sep e v default [] (Ne.symm hz) (by
    intro s hs
    simp only [v, List.mem_append, List.mem_cons, List.mem_replicate] at hs
    rcases hs with ⟨_,rfl⟩ | rfl | ⟨_,rfl⟩
    · exact haz
    · exact hsep
    · exact haz)
  have hh := hscan.trans (by
    simpa [TM0.Reaches, List.reverse_cons] using hmove)
  have hh := hh.trans hfill
  have hh := hh.trans (by
    simpa [TM0.Reaches, v, List.append_assoc] using hzero)
  have hh := hh.trans (by simpa [TM0.Reaches, v, List.append_assoc] using hback)
  have ht : Tape.mk₁ (z :: (v.reverse ++ [default])) =
      Tape.mk₁ (z :: (List.replicate q a ++ sep :: List.replicate e a)) := by
    change Tape.mk₂ [] ((z::v.reverse) ++ [default]) = _
    rw [trailing_blank]
    simp [Tape.mk₁, v, List.reverse_append, List.reverse_cons, List.append_assoc]
  have hh : TM0.Reaches (machine M a z sep e)
      ⟨.scan, Tape.mk₂ [] (z :: List.replicate q a)⟩
      ⟨.run default, Tape.mk₁ (z :: (v.reverse ++ [default]))⟩ := by
    simpa [TM0.Reaches, v, List.append_assoc] using hh
  rw [ht] at hh
  exact hh

def lift (c : TM0.Cfg Γ Q) : TM0.Cfg Γ (Label e Q) := ⟨.run c.q, c.Tape⟩

lemma step_lift (c : TM0.Cfg Γ Q) :
    (TM0.step M c).map (lift e) = TM0.step (machine M a z sep e) (lift e c) := by
  cases c with
  | mk q T =>
    simp only [TM0.step, machine, lift, Option.map_map]
    congr 1

lemma respects : StateTransition.Respects (TM0.step M) (TM0.step (machine M a z sep e))
    (fun c d => lift e c=d) := by
  intro c d hd
  subst d
  cases hs : TM0.step M c with
  | none => simpa [hs] using (step_lift M a z sep e c).symm
  | some c' =>
    refine ⟨lift e c', rfl, TransGen.single ?_⟩
    rw [← step_lift, hs]
    rfl

/-- Initialization adds no halting behavior and loses none. -/
theorem eval_dom (q : ℕ) (ha : a≠default) (hz : z≠default)
    (haz : a≠z) (hsep : sep≠z) :
    (TM0.eval (machine M a z sep e) (z :: List.replicate q a)).Dom ↔
      (TM0.eval M (z :: (List.replicate q a ++ sep :: List.replicate e a))).Dom := by
  have hh := handoff M a z sep e q ha hz haz hsep
  have he := StateTransition.reaches_eval hh
  change (StateTransition.eval (TM0.step (machine M a z sep e))
    (TM0.init (z :: List.replicate q a))).Dom ↔
      (StateTransition.eval (TM0.step M)
        (TM0.init (z :: (List.replicate q a ++ sep :: List.replicate e a)))).Dom
  rw [he]
  exact StateTransition.tr_eval_dom (respects M a z sep e) rfl

lemma body_ne_blank : SimulatorStandard.unaryBody ≠ default := by
  intro h
  have hh := congrArg (fun s : SimulatorMachine.TapeAlphabet => s.2 PartrecToTM2.K'.main) h
  simpa [SimulatorStandard.unaryBody] using hh

lemma bottom_ne_blank : SimulatorStandard.unaryBottom ≠ default := by
  intro h
  have hh := congrArg Prod.fst h
  simpa [SimulatorStandard.unaryBottom] using hh

lemma body_ne_bottom : SimulatorStandard.unaryBody ≠ SimulatorStandard.unaryBottom := by
  intro h
  have hh := congrArg Prod.fst h
  simpa [SimulatorStandard.unaryBody, SimulatorStandard.unaryBottom] using hh

lemma separator_ne_bottom : SimulatorPair.separator ≠ SimulatorStandard.unaryBottom := by
  intro h
  have hh := congrArg Prod.fst h
  simpa [SimulatorPair.separator, SimulatorStandard.unaryBottom] using hh

/-- A single fixed verifier with only the explicit finite initialization
controller varying in e. All prescribed-seed correctness clauses hold. -/
theorem program_family (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Inhabited Q) (_ : DecidableEq Q)
      (M : TM0.Machine SimulatorMachine.TapeAlphabet Q), ∀ e,
      Sigma2.Reduction.ProgramCorrect R e
        (SimulatorLoader.automaton (machine M SimulatorStandard.unaryBody
          SimulatorStandard.unaryBottom SimulatorPair.separator e)
          SimulatorStandard.unaryBody SimulatorStandard.unaryBottom) := by
  classical
  obtain ⟨Q, fQ, iQ, M, hM⟩ := SimulatorPair.finite_verifier R hR
  letI := fQ
  letI := iQ
  letI : DecidableEq Q := Classical.decEq Q
  refine ⟨Q, fQ, iQ, inferInstance, M, fun e => ⟨?_,?_,?_⟩⟩
  · intro q hq
    rw [SimulatorStandard.no_reject_iff _ _ _ q hq]
    rw [eval_dom M SimulatorStandard.unaryBody SimulatorStandard.unaryBottom
      SimulatorPair.separator e q body_ne_blank bottom_ne_blank body_ne_bottom separator_ne_bottom]
    rw [← SimulatorPair.input_pair e q, hM e q, not_not]
  · intro q hq t ht x
    exact SimulatorLoader.initial_safe _ _ _ q hq t x (by omega)
  · exact Sigma2.Tree.run_blank _

#print axioms program_family
#print axioms handoff
#print axioms eval_dom
end Sigma2.SimulatorParameter






