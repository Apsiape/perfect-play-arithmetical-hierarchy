import Sigma2.UpperEntropySyntax

set_option maxHeartbeats 400000
set_option maxRecDepth 2000
namespace Sigma2.UpperEntropyEffective
open UpperRealArithmetic UpperStageSyntax UpperEntropySyntax UpperEffective UpperGameCompiler

/-- Total computable finite maps, proved by an explicit list-building recursion. -/
@[fun_prop] theorem rangeMap_computable {α β : Type*} [Primcodable α] [Primcodable β]
    (n : α → ℕ) (f : α → ℕ → β) (hn : Computable n)
    (hf : Computable (fun p : α × ℕ => f p.1 p.2)) :
    Computable (fun a => (List.range (n a)).map (f a)) := by
  have hs : Computable (fun p : α × (ℕ × List β) => p.2.2 ++ [f p.1 p.2.1]) :=
    Computable.list_append.comp (Computable.snd.comp Computable.snd)
      (Computable.list_cons.comp
        (hf.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
        (Computable.const []))
  refine (Computable.nat_rec hn (Computable.const []) hs.to₂).of_eq ?_
  intro a
  induction n a with
  | zero => rfl
  | succ k ih => simp [ih,List.range_succ]

@[fun_prop] theorem rtotal_computable {α : Type*} [Primcodable α]
    (n : α → ℕ) (f : α → ℕ → Poly) (hn : Computable n)
    (hf : Computable (fun p : α × ℕ => f p.1 p.2)) :
    Computable (fun a => rtotal (n a) (f a)) :=
  sum_primrec.to_comp.comp (rangeMap_computable n f hn hf)

@[fun_prop] theorem bounded_computable {α : Type*} [Primcodable α]
    (n : α → ℕ) (f : α → ℕ → Sentence) (hn : Computable n)
    (hf : Computable (fun p : α × ℕ => f p.1 p.2)) :
    Computable (fun a => bounded (n a) (f a)) :=
  Primrec.list_flatten.to_comp.comp (rangeMap_computable n f hn hf)

@[fun_prop] theorem pvar_primrec : Primrec pvar := by unfold pvar; fun_prop
@[fun_prop] theorem power_primrec : Primrec (fun p : Poly × ℕ => power p.1 p.2) := by
  unfold power
  exact Primrec.nat_rec' Primrec.snd (Primrec.const (constant 1))
    (mul_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂

@[fun_prop] theorem coefficient_computable :
    Computable (fun p : List (ℤ × ℕ) × ℕ => coefficient p.1 p.2) := by
  have hg : Primrec (fun p : List (ℤ × ℕ) × ℕ => p.1[p.2]?.getD (0,0)) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd)
      (Primrec.const (0,0))
  exact UpperCoding.rat_fraction.comp hg.to_comp

@[fun_prop] theorem approximation_computable :
    Computable (fun p : List (ℤ × ℕ) × Poly => approximation p.1 p.2) := by
  unfold approximation
  apply rtotal_computable <;> fun_prop

@[fun_prop] theorem simplex_primrec : Primrec simplex := by unfold simplex; fun_prop
@[fun_prop] theorem event_primrec :
    Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => event p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold event
  fun_prop
attribute [local irreducible] UpperEntropySyntax.event

@[fun_prop] theorem lossPoly_primrec : Primrec (fun p : RawGame × ℕ => lossPoly p.1 p.2) := by
  unfold lossPoly
  apply pr_rtotal
  · fun_prop
  · apply pr_rtotal
    · fun_prop
    · apply pr_rtotal
      · fun_prop
      · apply pr_rtotal
        · fun_prop
        · apply pr_ite_bool
          · fun_prop
          · exact Primrec.const (constant 0)
          · refine mul_primrec.comp ?_ ?_
            · fun_prop
            · have hi : Primrec (fun p : ((((RawGame × ℕ) × ℕ) × ℕ) × ℕ) × ℕ =>
                  (p.1.1.1.1.2,p.1.1.1.2,p.1.1.2,p.1.2,p.2)) := by fun_prop
              have hEv := event_primrec.comp hi
              have hReal := (Primrec.fst : Primrec (@Prod.fst Poly Poly)).comp hEv
              exact hReal.of_eq (fun p => rfl)

@[fun_prop] theorem ratAdd_computable : Computable (fun p : ℚ × ℚ => p.1+p.2) :=
  UpperCoding.rat_add
@[fun_prop] theorem rationalSlack_computable : Computable (fun n : ℕ => (1:ℚ)/(n+1:ℚ)) := by
  refine (UpperCoding.rat_fraction.comp
    ((Computable.const (1:ℤ)).pair Computable.id)).of_eq ?_
  intro n
  simp

@[fun_prop] theorem append_computable {α : Type*} [Primcodable α] :
    Computable (fun p : List α × List α => p.1 ++ p.2) := Primrec.list_append.to_comp
@[fun_prop] theorem simplex_computable : Computable simplex := simplex_primrec.to_comp
@[fun_prop] theorem normalizationE_computable : Computable (fun p : ℕ × ℕ × ℕ =>
    normalization p.1 p.2.1 p.2.2 (evar p.2.2)) := pr_normalizationE.to_comp
@[fun_prop] theorem normalizationF_computable : Computable (fun p : ℕ × ℕ × ℕ =>
    normalization p.1 p.2.1 p.2.2 (fvar p.2.2)) := pr_normalizationF.to_comp
@[fun_prop] theorem lossPoly_computable : Computable (fun p : RawGame × ℕ => lossPoly p.1 p.2) :=
  lossPoly_primrec.to_comp

abbrev Input := RawGame × ℕ × ℕ × ℕ × ℚ × List (ℤ × ℕ)
abbrev CodeInput := ℕ × ℕ × ℕ × ℕ × ℚ × List (ℤ × ℕ)

attribute [local irreducible] UpperEntropySyntax.simplex UpperEntropySyntax.lossPoly
  UpperEntropySyntax.approximation UpperEntropySyntax.pvar

theorem sentence_computable : Computable (fun p : Input =>
    UpperEntropySyntax.sentence p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  have hn : Primrec (fun p : Input => p.2.2.1) := by fun_prop
  have hk : Primrec (fun p : Input => p.2.2.2.1) := by fun_prop
  have hB : Primrec (fun p : Input => p.2.1) := by fun_prop
  have hm := (Primrec.succ.comp hn).to_comp
  have hqa : Primrec (fun p : Input => p.1.1.questionsA+1) := by fun_prop
  have hqb : Primrec (fun p : Input => p.1.1.questionsB+1) := by fun_prop
  have haa : Primrec (fun p : Input => p.1.1.answersA+1) := by fun_prop
  have hbb : Primrec (fun p : Input => p.1.1.answersB+1) := by fun_prop
  have hη : Computable (fun p : Input => p.2.2.2.2.1) := by fun_prop
  have hc : Computable (fun p : Input => p.2.2.2.2.2) := by fun_prop
  have hS := simplex_computable.comp hm
  have hE := normalizationE_computable.comp (hqa.to_comp.pair (haa.to_comp.pair hm))
  have hF := normalizationF_computable.comp (hqb.to_comp.pair (hbb.to_comp.pair hm))
  have hL := pr_le.to_comp.comp
    ((lossPoly_computable.comp (Computable.fst.pair hm)).pair
      (constant_primrec.to_comp.comp hη))
  have hA : Computable (fun p : Input × ℕ => approximation p.1.2.2.2.2.2 (pvar p.2)) :=
    approximation_computable.comp ((hc.comp Computable.fst).pair
      (pvar_primrec.to_comp.comp Computable.snd))
  have hsum := rtotal_computable (fun p : Input => p.2.2.1+1)
    (fun p i => approximation p.2.2.2.2.2 (pvar i)) hm hA
  have hbudget := ratAdd_computable.comp
    ((ratAdd_computable.comp ((pr_rat_natCast.to_comp.comp hB.to_comp).pair
      (rationalSlack_computable.comp hn.to_comp))).pair
      (rationalSlack_computable.comp hk.to_comp))
  have hH := pr_le.to_comp.comp (hsum.pair (constant_primrec.to_comp.comp hbudget))
  exact Computable.list_append.comp
    (Computable.list_append.comp (Computable.list_append.comp
      (Computable.list_append.comp hS hE) hF) hL) hH

/-- Invalid encodings yield the empty disjunction, so they are uniformly rejected. -/
def codeSentence (c B n k : ℕ) (η : ℚ) (a : List (ℤ × ℕ)) : OrderedRingSentence :=
  ((Encodable.decode (α := RawGame) c).map fun r =>
    if ValidRawGame r then conjunctive (UpperEntropySyntax.sentence r B n k η a) else []).getD []

theorem codeSentence_computable : Computable (fun p : CodeInput =>
    codeSentence p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  have ha : Computable (fun p : CodeInput × RawGame => (p.2,p.1.2)) :=
    Computable.snd.pair (Computable.snd.comp Computable.fst)
  have hs := conjunctive_primrec.to_comp.comp (sentence_computable.comp ha)
  have hc : Computable (fun p : CodeInput × RawGame => decide (ValidRawGame p.2)) :=
    validity_computable.decide.comp Computable.snd
  have hg := hc.cond hs (Computable.const [])
  have hd : Computable (fun p : CodeInput => Encodable.decode (α := RawGame) p.1) :=
    Computable.decode.comp Computable.fst
  refine (Computable.option_getD (Computable.option_map hd hg.to₂) (Computable.const [])).of_eq ?_
  intro p
  simp only [Bool.cond_decide]
  rfl

end Sigma2.UpperEntropyEffective


