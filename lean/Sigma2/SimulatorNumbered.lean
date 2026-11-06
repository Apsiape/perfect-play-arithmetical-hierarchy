import Sigma2.SimulatorUniform

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorNumbered
open Sigma2.Tree Sigma2.Reduction

/-- A chosen, possibly redundant numbering. The inverse law is explicit. -/
structure Coding (A : Type) where
  size : ℕ
  pos : 0<size
  enc : A → ℕ
  enc_lt : ∀ a, enc a<size
  dec : ℕ → A
  left_inv : Function.LeftInverse dec enc

namespace Coding
variable {A B : Type}
@[simp] lemma dec_enc (C : Coding A) (a : A) : C.dec (C.enc a)=a := C.left_inv a

def fixed (A : Type) [Fintype A] [Nonempty A] : Coding A where
  size := Fintype.card A
  pos := Fintype.card_pos
  enc := fun a => (Fintype.equivFin A a).val
  enc_lt := fun a => (Fintype.equivFin A a).isLt
  dec := fun n => (Fintype.equivFin A).symm ⟨n%Fintype.card A, Nat.mod_lt _ Fintype.card_pos⟩
  left_inv := by intro a; simp [Nat.mod_eq_of_lt]

def prod (C : Coding A) (D : Coding B) : Coding (A × B) where
  size := C.size*D.size
  pos := Nat.mul_pos C.pos D.pos
  enc := fun p => C.enc p.1 * D.size + D.enc p.2
  enc_lt := fun p => SimulatorEncoding.pack_lt (C.enc_lt p.1) (D.enc_lt p.2)
  dec := fun n => (C.dec (n/D.size), D.dec (n%D.size))
  left_inv := by
    intro p
    simp only [SimulatorEncoding.pack_div _ _ _ D.pos (D.enc_lt p.2),
      SimulatorEncoding.pack_mod _ _ _ (D.enc_lt p.2), Coding.dec_enc]

def option (C : Coding A) : Coding (Option A) where
  size := C.size+1
  pos := by omega
  enc := fun a => match a with | none => 0 | some a => C.enc a+1
  enc_lt := by
    intro a
    cases a with
    | none => change 0<C.size+1; omega
    | some a => change C.enc a+1<C.size+1; exact Nat.succ_lt_succ (C.enc_lt a)
  dec := fun n => if n=0 then none else some (C.dec (n-1))
  left_inv := by intro a; cases a <;> simp [C.left_inv]
end Coding

variable {A : Type} [DecidableEq A] (D : SimulatorAlphabet.Rule A) (C : Coding A)

def encode (a : A) : Fin (C.size+3) :=
  if a=D.start then ⟨0,by omega⟩ else
  if a=D.blank then ⟨1,by omega⟩ else
  if a=D.reject then ⟨2,by omega⟩ else
  ⟨C.enc a+3, by have := C.enc_lt a; omega⟩

def decode (a : Fin (C.size+3)) : A :=
  if a.val=0 then D.start else
  if a.val=1 then D.blank else
  if a.val=2 then D.reject else C.dec (a.val-3)

@[simp] theorem encode_start : encode D C D.start = 0 := by simp [encode]
@[simp] theorem encode_blank : encode D C D.blank = 1 := by
  simp [encode, Ne.symm D.start_ne_blank]
@[simp] theorem encode_reject : encode D C D.reject = 2 := by
  apply Fin.ext
  simp [encode, Ne.symm D.start_ne_reject, Ne.symm D.blank_ne_reject,
    Nat.mod_eq_of_lt (show 2<C.size+3 by omega)]
@[simp] theorem decode_zero : decode D C 0 = D.start := by simp [decode]
@[simp] theorem decode_one : decode D C 1 = D.blank := by simp [decode]
@[simp] theorem decode_two : decode D C 2 = D.reject := by
  simp [decode, Nat.mod_eq_of_lt (show 2<C.size+3 by omega)]

@[simp] theorem decode_encode (a : A) : decode D C (encode D C a) = a := by
  by_cases hs : a=D.start
  · subst a; simp
  by_cases hb : a=D.blank
  · subst a; simp
  by_cases hr : a=D.reject
  · subst a; simp
  have h0 : ¬ C.enc a+3=0 := by omega
  have h1 : ¬ C.enc a+3=1 := by omega
  have h2 : ¬ C.enc a+3=2 := by omega
  simp [encode, decode, hs, hb, hr, h0, h1, h2, C.left_inv]

theorem encode_injective : Function.Injective (encode D C) :=
  Function.LeftInverse.injective (decode_encode D C)

def automaton : Automaton where
  extraSymbols := C.size
  update := fun l c r b =>
    if l=some 1 ∧ c=1 ∧ r=1 then 1 else
    encode D C (D.update (l.map (decode D C)) (decode D C c) (decode D C r) b)
  blank_quiescence := by intro b; simp

lemma decode_update (l : Option (Symbol (automaton D C)))
    (c r : Symbol (automaton D C)) (b : Bool) :
    decode D C ((automaton D C).update l c r b) =
      D.update (l.map (decode D C)) (decode D C c) (decode D C r) b := by
  change decode D C (if l=some 1 ∧ c=1 ∧ r=1 then 1 else _) = _
  split_ifs with h
  · rcases h with ⟨rfl,rfl,rfl⟩
    simpa using (D.quiescence b).symm
  · exact decode_encode D C _

lemma decode_run (pulse : ℕ → Bool) (t x : ℕ) :
    decode D C (run (automaton D C) pulse t x) = SimulatorAlphabet.typedRun D pulse t x := by
  induction t generalizing x with
  | zero => by_cases hx : x=0 <;> simp [run, SimulatorAlphabet.typedRun, hx]
  | succ t ih =>
    simp only [run, decode_update, SimulatorAlphabet.typedRun]
    by_cases hx : x=0 <;> simp [ih, hx]

lemma run_encode (pulse : ℕ → Bool) (t x : ℕ) :
    encode D C (SimulatorAlphabet.typedRun D pulse t x) =
      run (automaton D C) pulse t x := by
  rw [← decode_run D C]
  cases t with
  | zero => by_cases hx : x=0 <;> simp [run, hx]
  | succ t =>
    simp only [run, automaton]
    split_ifs <;> simp_all

lemma reject_iff (pulse : ℕ → Bool) (t x : ℕ) :
    run (automaton D C) pulse t x=2 ↔ SimulatorAlphabet.typedRun D pulse t x=D.reject := by
  rw [← run_encode D C, ← encode_reject D C]
  exact (encode_injective D C).eq_iff

/-- Transfer the frozen full correctness predicate to any explicit numbering. -/
theorem programCorrect [Fintype A] (R : ℕ × ℕ × ℕ → Bool) (e : ℕ)
    (h : ProgramCorrect R e (SimulatorAlphabet.automaton D)) :
    ProgramCorrect R e (automaton D C) := by
  have he (pulse : ℕ → Bool) (t x : ℕ) :
      run (automaton D C) pulse t x=2 ↔ run (SimulatorAlphabet.automaton D) pulse t x=2 := by
    rw [reject_iff, ← SimulatorLoader.run_encode, ← SimulatorAlphabet.encode_reject D]
    exact (SimulatorAlphabet.encode_injective D).eq_iff.symm
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    simpa only [ne_eq, he] using h.1 q hq
  · intro q hq t ht x
    exact fun hx => h.2.1 q hq t ht x ((he _ _ _).mp hx)
  · exact run_blank _

#print axioms programCorrect
end Sigma2.SimulatorNumbered

