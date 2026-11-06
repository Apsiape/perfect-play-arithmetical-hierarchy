import Sigma2.CompilerEffectivePresentation
import Sigma2.CompilerEffectiveBool
noncomputable section
set_option maxHeartbeats 150000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList polynomials
  structuralPolynomials applicationPolynomials
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair
  Computable.sumInl Computable.sumInr Computable.sumCasesOn Computable.cond

abbrev QuestionData := ProjectionName ⊕ (ℕ × ℕ) ⊕ (ℕ × ℕ) ⊕ Unit

def questionEquiv : Question ≃ QuestionData where
  toFun
    | .binary p => .inl p
    | .fms g x => .inr (.inl (g,x))
    | .refinement g k => .inr (.inr (.inl (g,k)))
    | .padding => .inr (.inr (.inr ()))
  invFun
    | .inl p => .binary p
    | .inr (.inl (g,x)) => .fms g x
    | .inr (.inr (.inl (g,k))) => .refinement g k
    | .inr (.inr (.inr _)) => .padding
  left_inv := by intro q; cases q <;> rfl
  right_inv := by intro q; rcases q with p | ⟨g,x⟩ | ⟨g,k⟩ | ⟨⟩ <;> rfl

instance questionPrimcodable : Primcodable Question := Primcodable.ofEquiv QuestionData questionEquiv
@[local fun_prop] theorem question_forward : Computable questionEquiv := Primrec.of_equiv.to_comp
@[local fun_prop] theorem question_back : Computable questionEquiv.symm := Primrec.of_equiv_symm.to_comp

variable {α β : Type} [Primcodable α] [Primcodable β]

@[fun_prop] theorem cBinary (p : α → ProjectionName) (hp : Computable p) :
    Computable (fun a => Question.binary (p a)) := by
  change Computable (fun a => questionEquiv.symm (Sum.inl (p a)))
  fun_prop
@[fun_prop] theorem cFms (g x : α → ℕ) (hg : Computable g) (hx : Computable x) :
    Computable (fun a => Question.fms (g a) (x a)) := by
  change Computable (fun a => questionEquiv.symm (Sum.inr (Sum.inl (g a,x a))))
  fun_prop
@[fun_prop] theorem cRefinement (g k : α → ℕ) (hg : Computable g) (hk : Computable k) :
    Computable (fun a => Question.refinement (g a) (k a)) := by
  change Computable (fun a => questionEquiv.symm (Sum.inr (Sum.inr (Sum.inl (g a,k a)))))
  fun_prop

def questionMatch (q : Question) (b : ProjectionName → β) (f r : ℕ × ℕ → β) (p : β) : β :=
  match q with
  | .binary n => b n
  | .fms g x => f (g,x)
  | .refinement g k => r (g,k)
  | .padding => p

theorem cquestionMatch (q : α → Question) (b : α × ProjectionName → β)
    (f r : α × (ℕ × ℕ) → β) (p : α → β)
    (hq : Computable q) (hb : Computable b) (hf : Computable f)
    (hr : Computable r) (hp : Computable p) :
    Computable (fun a => questionMatch (q a) (fun n => b (a,n))
      (fun gx => f (a,gx)) (fun gk => r (a,gk)) (p a)) := by
  have hh : Computable (fun z : α × QuestionData =>
      Sum.casesOn (motive := fun _ => β) z.2 (fun n => b (z.1,n)) (fun t =>
        Sum.casesOn (motive := fun _ => β) t (fun gx => f (z.1,gx)) (fun t =>
          Sum.casesOn (motive := fun _ => β) t (fun gk => r (z.1,gk)) (fun _ => p z.1)))) := by fun_prop
  have hc := hh.comp (Computable.id.pair (question_forward.comp hq))
  exact hc.of_eq (fun a => by cases q a <;> rfl)

theorem finite_traversals :
    Computable rowList ∧ Computable names ∧ Computable (fun P => (scenario P).questionsA) ∧
    Computable (fun P => (1:ℚ) / (((scenario P).questionsA+1)*((scenario P).questionsB+1) : ℕ)) :=
  CompilerEffective.finite_traversals_from_original_fields id fields_primrec.to_comp

@[fun_prop] theorem rowList_computable : Computable rowList := finite_traversals.1
@[fun_prop] theorem names_computable : Computable names := finite_traversals.2.1
@[fun_prop] theorem pre_count_computable : Computable (fun P => (scenario P).questionsA) := finite_traversals.2.2.1

theorem encodingCount_computable : Computable encodingCount := by
  have ht : Computable (fun P : Presentation => Encodable.encode P.types) :=
    (Computable.fst.comp fields_primrec.to_comp).of_eq (fun _ => rfl)
  exact encodingCount_family_computable id
    (list_map_computable_of_code (fun t : LabelType => Encodable.encode t) (fun _ => rfl) (fun P : Presentation => P.types) ht)
attribute [local fun_prop] encodingCount_computable

@[fun_prop] theorem crefCount (P : α → Presentation) (hP : Computable P) :
    Computable (fun a => refinementCount (P a)) := by
  have he := encodingCount_computable.comp hP
  unfold refinementCount
  fun_prop

theorem question_computable : Computable (fun z : Presentation × ℕ => question z.1 z.2) := by
  unfold question
  fun_prop
@[fun_prop] theorem cquestion (P : α → Presentation) (x : α → ℕ) (hP : Computable P) (hx : Computable x) :
    Computable (fun a => question (P a) (x a)) := question_computable.comp (hP.pair hx)

theorem valid_computable : Computable (fun z : Question × ℕ => valid z.1 z.2) := by
  have hc := cquestionMatch (fun z : Question × ℕ => z.1)
    (fun z => decide (z.1.2<2)) (fun z => decide (z.1.2<6))
    (fun z => decide (z.1.2<12)) (fun z => decide (z.2=0))
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  exact hc.of_eq (fun z => by cases z.1 <;> rfl)
@[fun_prop] theorem cvalid (q : α → Question) (a : α → ℕ) (hq : Computable q) (ha : Computable a) :
    Computable (fun z => valid (q z) (a z)) := valid_computable.comp (hq.pair ha)

@[fun_prop] theorem clist_all (f : α → List β) (p : α → β → Bool)
    (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a => (f a).all (p a)) := call f (fun z => p z.1 z.2) hf hp

#print axioms questionPrimcodable
#print axioms finite_traversals
#print axioms question_computable
#print axioms valid_computable
end Sigma2.CompilerEffectiveCoding