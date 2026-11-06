import Sigma2.UpperGameCompiler

namespace Sigma2.UpperGameCompiler
open Sigma2.UpperStageSyntax Sigma2.UpperRealArithmetic Sigma2.UpperEffective Primrec
open scoped BigOperators
set_option maxHeartbeats 200000

def allN (n : ℕ) (P : ℕ → Bool) : Bool := (List.range n).foldr (fun i acc => P i && acc) true

theorem allN_true (n : ℕ) (P : ℕ → Bool) : allN n P = true ↔ ∀ i : Fin n,P i = true := by
  have h (xs : List ℕ) : xs.foldr (fun i acc => P i && acc) true = true ↔ ∀ i ∈ xs,P i = true := by
    induction xs with
    | nil => simp
    | cons i xs ih => simp [ih]
  rw [allN,h]
  simp only [List.mem_range]
  exact ⟨fun h i => h i i.isLt,fun h i hi => h ⟨i,hi⟩⟩

@[fun_prop] theorem allN_primrec {α : Type*} [Primcodable α]
    (n : α → ℕ) (P : α → ℕ → Bool) (hn : Primrec n)
    (hP : Primrec (fun p : α × ℕ => P p.1 p.2)) : Primrec (fun p => allN (n p) (P p)) := by
  exact list_foldr (list_range.comp hn) (const true)
    (bool_and_primrec.comp ((hP.comp (fst.pair (fst.comp snd))).pair (snd.comp snd))).to₂

def qsum (n : ℕ) (f : ℕ → ℚ) : ℚ := Nat.rec 0 (fun i acc => acc + f i) n

theorem qsum_eq (n : ℕ) (f : ℕ → ℚ) : qsum n f = ∑ i : Fin n,f i := by
  induction n with
  | zero => simp [qsum]
  | succ n ih => simpa [qsum,Fin.sum_univ_castSucc] using congrArg (· + f n) ih

attribute [fun_prop] Computable
attribute [fun_prop] Computable.id Computable.const Computable.comp Computable.pair Computable.fst Computable.snd
attribute [fun_prop] Primrec.to_comp

@[fun_prop] theorem qsum_computable {α : Type*} [Primcodable α]
    (n : α → ℕ) (f : α → ℕ → ℚ) (hn : Computable n)
    (hf : Computable (fun p : α × ℕ => f p.1 p.2)) : Computable (fun p => qsum (n p) (f p)) := by
  exact Computable.nat_rec hn (Computable.const 0)
    (UpperCoding.rat_add.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))).to₂

def weightTotal (r : RawGame) : ℚ :=
  qsum (r.1.questionsA+1) fun x => qsum (r.1.questionsB+1) (rawWeight r x)
def nonnegative (r : RawGame) : Bool :=
  allN (r.1.questionsA+1) fun x => allN (r.1.questionsB+1) fun y => decide (0 ≤ rawWeight r x y)
def valid (r : RawGame) : Bool :=
  decide (r.2.1.length = (r.1.questionsA+1)*(r.1.questionsB+1)) &&
  decide (r.2.2.length = (r.1.questionsA+1)*(r.1.questionsB+1)*(r.1.answersA+1)*(r.1.answersB+1)) &&
  nonnegative r && decide (weightTotal r = 1)

@[fun_prop] theorem rational_nonnegative_primrec : Primrec (fun q : ℚ => decide (0 ≤ q)) := by
  exact ((UpperCoding.rat_lt.comp .id (const 0)).not.of_eq (fun q => not_lt)).decide
@[fun_prop] theorem length_primrec {α : Type*} [Primcodable α] : Primrec (@List.length α) := list_length
@[fun_prop] theorem nat_eq_primrec : Primrec (fun p : ℕ × ℕ => decide (p.1 = p.2)) := Primrec.eq.decide
@[fun_prop] theorem nonnegative_primrec : Primrec nonnegative := by
  have hqa : Primrec (fun r : RawGame => r.1.questionsA+1) :=
    Primrec.succ.comp (questionsA_primrec.comp fst)
  have hqb : Primrec (fun p : RawGame × ℕ => p.1.1.questionsB+1) :=
    Primrec.succ.comp (questionsB_primrec.comp (fst.comp fst))
  have hp : Primrec (fun p : (RawGame × ℕ) × ℕ => (p.1.1,p.1.2,p.2)) :=
    (fst.comp fst).pair ((snd.comp fst).pair snd)
  have hw := rawWeight_primrec.comp hp
  have hn := rational_nonnegative_primrec.comp hw
  have hi := allN_primrec (fun p : RawGame × ℕ => p.1.1.questionsB+1)
    (fun p y => decide (0 ≤ rawWeight p.1 p.2 y)) hqb hn
  have ho := allN_primrec (fun r : RawGame => r.1.questionsA+1)
    (fun r x => allN (r.1.questionsB+1) fun y => decide (0 ≤ rawWeight r x y)) hqa hi
  exact ho
@[fun_prop] theorem weightTotal_computable : Computable weightTotal := by unfold weightTotal; fun_prop

@[fun_prop] theorem rational_eq_computable : Computable (fun p : ℚ × ℚ => decide (p.1 = p.2)) :=
  Primrec.eq.decide.to_comp
theorem valid_computable : Computable valid := by
  have hqa : Primrec (fun r : RawGame => r.1.questionsA+1) := Primrec.succ.comp (questionsA_primrec.comp fst)
  have hqb : Primrec (fun r : RawGame => r.1.questionsB+1) := Primrec.succ.comp (questionsB_primrec.comp fst)
  have haa : Primrec (fun r : RawGame => r.1.answersA+1) := Primrec.succ.comp (answersA_primrec.comp fst)
  have hbb : Primrec (fun r : RawGame => r.1.answersB+1) := Primrec.succ.comp (answersB_primrec.comp fst)
  have hl1 : Primrec (fun r : RawGame => r.2.1.length) := list_length.comp (fst.comp snd)
  have hl2 : Primrec (fun r : RawGame => r.2.2.length) := list_length.comp (snd.comp snd)
  have hp1 := nat_mul.comp hqa hqb
  have hp2 := nat_mul.comp (nat_mul.comp hp1 haa) hbb
  have he1 := (Primrec.eq.comp hl1 hp1).decide
  have he2 := (Primrec.eq.comp hl2 hp2).decide
  have hshape := bool_and_primrec.comp ((bool_and_primrec.comp (he1.pair he2)).pair nonnegative_primrec)
  have hp := weightTotal_computable.pair (Computable.const (1:ℚ))
  have hsum := rational_eq_computable.comp hp
  have hv := bool_and_primrec.to_comp.comp (hshape.to_comp.pair hsum)
  exact hv

theorem valid_iff (r : RawGame) : valid r = true ↔ ValidRawGame r := by
  simp only [valid,Bool.and_eq_true,decide_eq_true_eq,nonnegative,allN_true,ValidRawGame,
    weightTotal,qsum_eq]
  dsimp only [rawWeight,rawDistribution]
  tauto

theorem validity_computable : ComputablePred ValidRawGame :=
  (Computable.computablePred valid_computable).of_eq valid_iff

/-- Invalid codes produce the empty disjunction, hence False. -/
def codeSentence (c κ n : ℕ) : OrderedRingSentence :=
  ((Encodable.decode (α := RawGame) c).map fun r =>
    if ValidRawGame r then conjunctive (sentence r.1 κ n (rawLosing r)) else []).getD []

theorem codeSentence_computable : Computable (fun p : ℕ × ℕ × ℕ => codeSentence p.1 p.2.1 p.2.2) := by
  have ha : Computable (fun p : (ℕ × ℕ × ℕ) × RawGame => (p.2,p.1.2.1,p.1.2.2)) :=
    Computable.snd.pair ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hs0 := sentence_computable.comp ha
  have hs := conjunctive_primrec.to_comp.comp hs0
  have hc : Computable (fun p : (ℕ × ℕ × ℕ) × RawGame => decide (ValidRawGame p.2)) :=
    validity_computable.decide.comp Computable.snd
  have hg := hc.cond hs (Computable.const [])
  have hd : Computable (fun p : ℕ × ℕ × ℕ => Encodable.decode (α := RawGame) p.1) :=
    Computable.decode.comp Computable.fst
  have hm := Computable.option_map hd hg.to₂
  have hres := Computable.option_getD hm (Computable.const [])
  refine hres.of_eq ?_
  intro p
  simp only [Bool.cond_decide]
  rfl
theorem codeSentence_truth (c κ n : ℕ) :
    OrderedRingTruth (codeSentence c κ n) ↔
      ∃ r : RawGame, Encodable.decode c = some r ∧ ValidRawGame r ∧ Witness r.1 κ n (rawLosing r) := by
  cases h : Encodable.decode (α := RawGame) c with
  | none => simp [codeSentence,h,OrderedRingTruth]
  | some r =>
      by_cases hr : ValidRawGame r
      · simp [codeSentence,h,hr,truth_sentence]
      · simp [codeSentence,h,hr,OrderedRingTruth]

end Sigma2.UpperGameCompiler