import Sigma2.CompilerEffectiveExpansion
/-! Exact downstream composition for the frozen scaffold. The family lemmas
state their remaining generator premises explicitly; they do not assume the
compiler admission or assert unconditional computability of codeMap. -/
noncomputable section
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffective
open CompilerScaffold
attribute [local irreducible] Nat.pair Encodable.encodeList
attribute [local irreducible] structuralPolynomials applicationPolynomials polynomials
  words rowList names graphRows wordRows bindingRows polynomialRow refinementCount
  finalGame preGame codeFor
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair
  Computable.option_some
  wordRows_computable polynomialRow_computable bindingRows_computable

variable {α : Type} [Primcodable α]

@[fun_prop] theorem ccornerIndex (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => cornerIndex (f a)) := by unfold cornerIndex; fun_prop

theorem words_family_computable (P : α → Presentation)
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun a => words (P a)) := by
  unfold words
  fun_prop

theorem rowList_family_computable (P : α → Presentation)
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun a => rowList (P a)) := by
  have hw := words_family_computable P hp
  unfold rowList
  fun_prop

theorem names_family_computable (P : α → Presentation)
    (he : Computable (fun a => encodingCount (P a)))
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun a => names (P a)) := by
  have hr := rowList_family_computable P hp
  have he' : Computable (fun z : (α × ℕ) × ℕ => encodingCount (P z.1.1)) :=
    he.comp (Computable.fst.comp Computable.fst)
  have hg : Computable (fun z : (α × ℕ) × ℕ =>
      ProjectionName.graph [(33+5*encodingCount (P z.1.1)+z.1.2*encodingCount (P z.1.1)+z.2,false)] 0 0) := by
    fun_prop
  have hinner : Computable (fun z : α × ℕ =>
      (List.range (encodingCount (P z.1))).map (fun l =>
        ProjectionName.graph [(33+5*encodingCount (P z.1)+z.2*encodingCount (P z.1)+l,false)] 0 0)) :=
    cmap _ _ (crange _ (he.comp Computable.fst)) hg
  have hgraphs : Computable (fun a => (List.range 4).flatMap (fun g =>
      (List.range (encodingCount (P a))).map (fun l =>
        ProjectionName.graph [(33+5*encodingCount (P a)+g*encodingCount (P a)+l,false)] 0 0))) :=
    cflat _ _ (Computable.const _) hinner
  unfold names
  fun_prop

def rowAt (P : Presentation) (k : ℕ) : RationalRow :=
  (rowList P)[k]?.getD (row [])
def nameAt (P : Presentation) (k : ℕ) : ProjectionName :=
  (names P)[k]?.getD (.frame 0)

theorem rowAt_family_computable (P : α → Presentation)
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun z : α × ℕ => rowAt (P z.1) z.2) := by
  have hr := rowList_family_computable P hp
  exact cgetD _ _
    (cget _ _ (hr.comp Computable.fst) Computable.snd) (Computable.const (row []))

theorem nameAt_family_computable (P : α → Presentation)
    (he : Computable (fun a => encodingCount (P a)))
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun z : α × ℕ => nameAt (P z.1) z.2) := by
  have hn := names_family_computable P he hp
  exact cgetD _ _
    (cget _ _ (hn.comp Computable.fst) Computable.snd) (Computable.const (ProjectionName.frame 0))

theorem rows_constant_eq (P : Presentation) (r : Fin (rowList P).length) :
    (rows P).constant r=(rowAt P r.val).constant := by
  simp [rows,rowAt,r.isLt]

theorem rows_coefficient_eq (P : Presentation) (r : Fin (rowList P).length)
    (i : Fin (names P).length) :
    (rows P).coefficient r i=coefficient (rowAt P r.val) (nameAt P i.val) := by
  simp [rows,rowAt,nameAt,r.isLt,i.isLt]

theorem row_constant_family_computable (P : α → Presentation)
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun z : α × ℕ => (rowAt (P z.1) z.2).constant) :=
  cconstant _ (rowAt_family_computable P hp)

theorem row_coefficient_family_computable (P : α → Presentation)
    (he : Computable (fun a => encodingCount (P a)))
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun z : α × ℕ × ℕ =>
      coefficient (rowAt (P z.1) z.2.1) (nameAt (P z.1) z.2.2)) := by
  have hr := rowAt_family_computable P hp
  have hn := nameAt_family_computable P he hp
  have hc := coefficient_computable.comp
    ((hr.comp (Computable.fst.pair (Computable.fst.comp Computable.snd))).pair
      (hn.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))))
  exact hc.of_eq (fun z => rfl)

theorem pre_question_count_computable (P : α → Presentation)
    (he : Computable (fun a => encodingCount (P a)))
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun a => (scenario (P a)).questionsA) := by
  have hn := names_family_computable P he hp
  unfold scenario refinementCount
  fun_prop

theorem pre_distribution_value_computable (P : α → Presentation)
    (he : Computable (fun a => encodingCount (P a)))
    (hp : Computable (fun a => polynomials (P a))) :
    Computable (fun a => (1:ℚ) /
      (((scenario (P a)).questionsA+1)*((scenario (P a)).questionsB+1) : ℕ)) := by
  have hq := pre_question_count_computable P he hp
  have hqb : Computable (fun a => (scenario (P a)).questionsB) := hq
  have hc : Computable (fun a =>
      (((scenario (P a)).questionsA+1)*((scenario (P a)).questionsB+1))) := by fun_prop
  exact (UpperCoding.rat_divNat.comp ((Computable.const (1:ℤ)).pair hc)).of_eq
    (fun a => by simp)

/-- The C5 assembly uses the existing RawGame serializer. Its explicit premises
remain obligations for the actual compiler; this is not the final codeMap theorem. -/
theorem codeMap_computable_of_uniform
    (s : ℕ → Scenario) (distribution : ℕ → ℕ → ℚ) (accepts : ℕ → ℕ → Bool)
    (hqa : Computable (fun n => (s n).questionsA))
    (hqb : Computable (fun n => (s n).questionsB))
    (haa : Computable (fun n => (s n).answersA))
    (hab : Computable (fun n => (s n).answersB))
    (hd : Computable₂ distribution) (ha : Computable₂ accepts)
    (hvalid : Computable (fun n => (Encodable.decode (α := Presentation) n).isSome))
    (hraw : ∀ n P, Encodable.decode (α := Presentation) n=some P →
      GameTableEffective.rawFamily s distribution accepts n=GameTable.raw (finalGame P)) :
    Computable codeMap := by
  have hc := GameTableEffective.codeFamily_computable s distribution accepts hqa hqb haa hab hd ha
  apply (hvalid.cond hc (Computable.const 0)).of_eq
  intro n
  cases h : Encodable.decode (α := Presentation) n with
  | none => simp [h,codeMap]
  | some P =>
    simp only [h,Option.isSome_some,Bool.cond_true,codeMap]
    unfold codeFor
    change Encodable.encode (GameTableEffective.rawFamily s distribution accepts n)=
      GameTable.code (finalGame P)
    rw [hraw n P h]
    rfl

end Sigma2.CompilerEffective
