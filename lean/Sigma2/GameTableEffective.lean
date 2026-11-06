import Sigma2.GameTable
import Sigma2.UpperCoding
import Mathlib.Tactic.FunProp

/-! Uniform finite-table serialization, preserving the frozen codecs.
The entry enumeration follows SimulatorUniform; the Scenario encoder is
identified with its existing derived encoder by definitional equality. -/
noncomputable section
namespace Sigma2.GameTableEffective

attribute [local fun_prop] Primrec Primrec₂ Primrec.id Primrec.const Primrec.fst Primrec.snd
  Primrec.comp Primrec.succ Primrec.pair

abbrev Fields := ℕ × ℕ × ℕ × ℕ

def fields (s : Scenario) : Fields :=
  (s.questionsA,s.questionsB,s.answersA,s.answersB)

def node (a b : ℕ) : ℕ := Nat.pair (Nat.succ (Nat.pair 0 a)) b

def fieldsCode (p : Fields) : ℕ :=
  node 0 (node p.1 (node p.2.1 (node p.2.2.1 (node p.2.2.2 0))))

@[local fun_prop] theorem nat_pair_primrec : Primrec (fun p : ℕ × ℕ => Nat.pair p.1 p.2) :=
  Primrec₂.natPair

@[local fun_prop] theorem node_primrec : Primrec (fun p : ℕ × ℕ => node p.1 p.2) := by
  unfold node
  fun_prop

@[local fun_prop] theorem fieldsCode_primrec : Primrec fieldsCode := by
  unfold fieldsCode
  fun_prop

/-- This is the original derived Scenario codec, not a replacement encoding. -/
theorem fieldsCode_eq_encode (s : Scenario) : fieldsCode (fields s)=Encodable.encode s := by
  cases s
  rfl

theorem scenario_encode_computable (s : ℕ → Scenario)
    (hqa : Computable (fun e => (s e).questionsA))
    (hqb : Computable (fun e => (s e).questionsB))
    (haa : Computable (fun e => (s e).answersA))
    (hab : Computable (fun e => (s e).answersB)) :
    Computable (fun e => Encodable.encode (s e)) := by
  have hfields : Computable (fun e => fields (s e)) := hqa.pair (hqb.pair (haa.pair hab))
  exact (fieldsCode_primrec.to_comp.comp hfields).of_eq
    (fun e => fieldsCode_eq_encode (s e))

/-- Bounded table generation retains its parameter at every recursive step. -/
def entries {α : Type} (entry : ℕ → ℕ → α) (e : ℕ) : ℕ → List α
  | 0 => []
  | n+1 => entries entry e n ++ [entry e n]

theorem entries_computable {α : Type} [Primcodable α] (entry : ℕ → ℕ → α)
    (hentry : Computable₂ entry) : Computable₂ (entries entry) := by
  have hs : Computable (fun z : (ℕ × ℕ) × (ℕ × List α) =>
      z.2.2 ++ [entry z.1.1 z.2.1]) :=
    Primrec.list_concat.to_comp.comp (Computable.snd.comp Computable.snd)
      (hentry.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
  have hh := Computable.nat_rec Computable.snd (Computable.const ([] : List α)) hs.to₂
  apply hh.of_eq
  intro z
  induction z.2 with
  | zero => rfl
  | succ n ih => change _ ++ [entry z.1 n] = _; rw [ih]; rfl

theorem entries_eq {α : Type} (entry : ℕ → ℕ → α) (e n : ℕ) :
    entries entry e n=(List.range n).map (entry e) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [entries,ih,List.range_succ]

theorem entries_ofFn {α : Type} (entry : ℕ → ℕ → α) (e n : ℕ) :
    entries entry e n=List.ofFn (fun k : Fin n => entry e k.val) := by
  rw [entries_eq]
  apply List.ext_getElem <;> simp

@[simp] theorem entries_length {α : Type} (entry : ℕ → ℕ → α) (e n : ℕ) :
    (entries entry e n).length=n := by simp [entries_eq]

@[simp] theorem entries_lookup {α : Type} (entry : ℕ → ℕ → α) (e n k : ℕ) (hk : k<n) :
    (entries entry e n)[k]?=some (entry e k) := by simp [entries_eq,hk]

def questionCount (s : Scenario) : ℕ := (s.questionsA+1)*(s.questionsB+1)
def outcomeCount (s : Scenario) : ℕ := questionCount s*(s.answersA+1)*(s.answersB+1)

def rawFamily (s : ℕ → Scenario) (distribution : ℕ → ℕ → ℚ)
    (accepts : ℕ → ℕ → Bool) (e : ℕ) : RawGame :=
  (s e,entries distribution e (questionCount (s e)),entries accepts e (outcomeCount (s e)))

def codeFamily (s : ℕ → Scenario) (distribution : ℕ → ℕ → ℚ)
    (accepts : ℕ → ℕ → Bool) (e : ℕ) : ℕ :=
  Encodable.encode (rawFamily s distribution accepts e)

/-- Computable counts and actual uniform table entries suffice for serialization.
There is no classical search for a game code in this function. -/
theorem codeFamily_computable (s : ℕ → Scenario) (distribution : ℕ → ℕ → ℚ)
    (accepts : ℕ → ℕ → Bool)
    (hqa : Computable (fun e => (s e).questionsA))
    (hqb : Computable (fun e => (s e).questionsB))
    (haa : Computable (fun e => (s e).answersA))
    (hab : Computable (fun e => (s e).answersB))
    (hd : Computable₂ distribution) (ha : Computable₂ accepts) :
    Computable (codeFamily s distribution accepts) := by
  have hq : Computable (fun e => questionCount (s e)) :=
    Primrec.nat_mul.to_comp.comp (Computable.succ.comp hqa) (Computable.succ.comp hqb)
  have ho : Computable (fun e => outcomeCount (s e)) :=
    Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp hq (Computable.succ.comp haa)) (Computable.succ.comp hab)
  have hdl : Computable (fun e => entries distribution e (questionCount (s e))) :=
    (entries_computable distribution hd).comp Computable.id hq
  have hal : Computable (fun e => entries accepts e (outcomeCount (s e))) :=
    (entries_computable accepts ha).comp Computable.id ho
  have hp : Computable (fun e => Nat.pair (Encodable.encode (s e))
      (Nat.pair (Encodable.encode (entries distribution e (questionCount (s e))))
        (Encodable.encode (entries accepts e (outcomeCount (s e)))))) :=
    Primrec₂.natPair.to_comp.comp (scenario_encode_computable s hqa hqb haa hab)
      (Primrec₂.natPair.to_comp.comp (Computable.encode.comp hdl) (Computable.encode.comp hal))
  exact hp

/-- Exact identification of the numeric family with the already specified games.
The premise is a finite-table equality; it does not assume any game-code choice. -/
theorem decodeFamily (s : ℕ → Scenario) (distribution : ℕ → ℕ → ℚ)
    (accepts : ℕ → ℕ → Bool) (G : ℕ → Game)
    (hraw : ∀ e, rawFamily s distribution accepts e=GameTable.raw (G e)) (e : ℕ) :
    decodeGame (codeFamily s distribution accepts e)=some (G e) := by
  unfold codeFamily
  rw [hraw e]
  exact GameTable.decode_code (G e)

theorem effective_of_uniform (s : ℕ → Scenario) (distribution : ℕ → ℕ → ℚ)
    (accepts : ℕ → ℕ → Bool) (G : ℕ → Game)
    (hqa : Computable (fun e => (s e).questionsA))
    (hqb : Computable (fun e => (s e).questionsB))
    (haa : Computable (fun e => (s e).answersA))
    (hab : Computable (fun e => (s e).answersB))
    (hd : Computable₂ distribution) (ha : Computable₂ accepts)
    (hraw : ∀ e, rawFamily s distribution accepts e=GameTable.raw (G e)) :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ e, decodeGame (f e)=some (G e) :=
  ⟨codeFamily s distribution accepts,codeFamily_computable s distribution accepts hqa hqb haa hab hd ha,
    decodeFamily s distribution accepts G hraw⟩

#print axioms fieldsCode_primrec
#print axioms fieldsCode_eq_encode
#print axioms scenario_encode_computable
#print axioms entries_computable
#print axioms entries_eq
#print axioms entries_ofFn
#print axioms entries_lookup
#print axioms codeFamily_computable
#print axioms decodeFamily
#print axioms effective_of_uniform
end Sigma2.GameTableEffective
