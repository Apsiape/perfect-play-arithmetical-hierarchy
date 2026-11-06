import Sigma2.SimulatorEncoding

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Sigma2.SimulatorAlphabet
open Sigma2.Tree

/-- A finite typed local rule with the three distinguished paper symbols. -/
structure Rule (A : Type) where
  start : A
  blank : A
  reject : A
  start_ne_blank : start ≠ blank
  start_ne_reject : start ≠ reject
  blank_ne_reject : blank ≠ reject
  update : Option A → A → A → Bool → A
  quiescence : ∀ b, update (some blank) blank blank b = blank

variable {A : Type} [Fintype A] [DecidableEq A] (D : Rule A)

lemma card_pos (E : Rule A) : 0 < Fintype.card A := Fintype.card_pos_iff.mpr ⟨E.start⟩

/-- Preserve 0, 1 and 2 exactly; other typed states use a finite enumeration. -/
def encode (a : A) : Fin (Fintype.card A+3) :=
  if a=D.start then ⟨0,by omega⟩ else
  if a=D.blank then ⟨1,by omega⟩ else
  if a=D.reject then ⟨2,by omega⟩ else
  ⟨(Fintype.equivFin A a).val+3, by have h := (Fintype.equivFin A a).isLt; omega⟩

def decode (a : Fin (Fintype.card A+3)) : A :=
  if a.val=0 then D.start else
  if a.val=1 then D.blank else
  if a.val=2 then D.reject else
  (Fintype.equivFin A).symm ⟨(a.val-3)%Fintype.card A, Nat.mod_lt _ (card_pos D)⟩

@[simp] theorem encode_start : encode D D.start = 0 := by simp [encode]
@[simp] theorem encode_blank : encode D D.blank = 1 := by
  simp [encode, Ne.symm D.start_ne_blank]
@[simp] theorem encode_reject : encode D D.reject = 2 := by
  apply Fin.ext
  simp [encode, Ne.symm D.start_ne_reject, Ne.symm D.blank_ne_reject,
    Nat.mod_eq_of_lt (show 2 < Fintype.card A+3 by omega)]
@[simp] theorem decode_zero : decode D 0 = D.start := by simp [decode]
@[simp] theorem decode_one : decode D 1 = D.blank := by simp [decode]
@[simp] theorem decode_two : decode D 2 = D.reject := by simp [decode, Nat.mod_eq_of_lt (show 2 < Fintype.card A+3 by omega)]

@[simp] theorem decode_encode (a : A) : decode D (encode D a) = a := by
  by_cases hs : a=D.start
  · subst a; simp
  by_cases hb : a=D.blank
  · subst a; simp
  by_cases hr : a=D.reject
  · subst a; simp
  have h0 : ¬ (Fintype.equivFin A a).val+3=0 := by omega
  have h1 : ¬ (Fintype.equivFin A a).val+3=1 := by omega
  have h2 : ¬ (Fintype.equivFin A a).val+3=2 := by omega
  simp [encode, decode, hs, hb, hr, h0, h1, h2, Nat.mod_eq_of_lt]

theorem encode_injective : Function.Injective (encode D) :=
  Function.LeftInverse.injective (decode_encode D)

/-- An actual automaton in the frozen TableauBasic interface. -/
def automaton : Automaton where
  extraSymbols := Fintype.card A
  update := fun l c r b =>
    if l=some 1 ∧ c=1 ∧ r=1 then 1 else
    encode D (D.update (l.map (decode D)) (decode D c) (decode D r) b)
  blank_quiescence := by intro b; simp

/-- Even redundant noncanonical symbol codes decode to the typed transition. -/
theorem decode_update (l : Option (Symbol (automaton D))) (c r : Symbol (automaton D))
    (b : Bool) :
    decode D ((automaton D).update l c r b) =
      D.update (l.map (decode D)) (decode D c) (decode D r) b := by
  change decode D (if l=some 1 ∧ c=1 ∧ r=1 then 1 else _) = _
  split_ifs with h
  · rcases h with ⟨rfl,rfl,rfl⟩
    simpa using (D.quiescence b).symm
  · exact decode_encode D _

def typedRun (pulse : ℕ → Bool) : ℕ → ℕ → A
  | 0,x => if x=0 then D.start else D.blank
  | t+1,x => D.update (if x=0 then none else some (typedRun pulse t (x-1)))
    (typedRun pulse t x) (typedRun pulse t (x+1)) (pulse t)

/-- The paper's prescribed start/blank run executes the typed automaton exactly. -/
theorem decode_run (pulse : ℕ → Bool) (t x : ℕ) :
    decode D (run (automaton D) pulse t x) = typedRun D pulse t x := by
  induction t generalizing x with
  | zero => by_cases hx : x=0 <;> simp [run, typedRun, hx]
  | succ t ih =>
    simp only [run, decode_update, typedRun]
    by_cases hx : x=0 <;> simp [ih, hx]

/-- The table is serialized in Reduction.decodeAutomaton's existing format. -/
theorem decode_code : Sigma2.Reduction.decodeAutomaton
    (SimulatorEncoding.code (automaton D)) = automaton D := SimulatorEncoding.decode_code _

/-- The same local rule with an explicitly prepared initial configuration. -/
def runFrom (M : Automaton) (pulse : ℕ → Bool) (seed : ℕ → Symbol M) : ℕ → ℕ → Symbol M
  | 0,x => seed x
  | t+1,x => M.update (if x=0 then none else some (runFrom M pulse seed t (x-1)))
    (runFrom M pulse seed t x) (runFrom M pulse seed t (x+1)) (pulse t)

/-- The original run is the special prescribed start/blank initialization. -/
theorem runFrom_standard (M : Automaton) (pulse : ℕ → Bool) (t x : ℕ) :
    runFrom M pulse (fun y => if y=0 then 0 else 1) t x = run M pulse t x := by
  induction t generalizing x with
  | zero => rfl
  | succ t ih => simp only [runFrom, run, ih]

#print axioms decode_encode
#print axioms decode_update
#print axioms decode_run
#print axioms decode_code
#print axioms runFrom_standard
end Sigma2.SimulatorAlphabet
