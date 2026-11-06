import Sigma2.CompilerEffectiveApplications
/-! Additive compiler computability entry point for this pass.
The original decoder and Boolean RowGame tables are still required to obtain
an unconditional proof of Computable CompilerScaffold.codeMap. -/
noncomputable section
namespace Sigma2.CompilerEffective
open CompilerScaffold
attribute [local irreducible] Nat.pair Encodable.encodeList
  structuralPolynomials applicationPolynomials polynomials words rowList names

/-- The full finite polynomial, row and name traversal is computable from the
original seven encoded fields. No Primcodable instance for Presentation or Expr
is substituted for their frozen derived encodings. -/
theorem finite_traversals_from_original_fields {α : Type} [Primcodable α]
    (P : α → Presentation)
    (hf : Computable (fun a => CompilerSyntaxCodes.fields (P a))) :
    Computable (fun a => rowList (P a)) ∧
    Computable (fun a => names (P a)) ∧
    Computable (fun a => (scenario (P a)).questionsA) ∧
    Computable (fun a => (1:ℚ) /
      (((scenario (P a)).questionsA+1)*((scenario (P a)).questionsB+1) : ℕ)) := by
  have ht : Computable (fun a => Encodable.encode (P a).types) :=
    (Computable.fst.comp hf).of_eq (fun _ => rfl)
  have hr : Computable (fun a => (P a).root) :=
    (Computable.fst.comp (Computable.snd.comp hf)).of_eq (fun _ => rfl)
  have hc : Computable (fun a => Encodable.encode (P a).central) :=
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hf)))).of_eq
      (fun _ => rfl)
  have he : Computable (fun a => Encodable.encode (P a).endpoints) :=
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp hf))))).of_eq (fun _ => rfl)
  have hz : Computable (fun a => Encodable.encode (P a).zeros) :=
    (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hf)))))).of_eq (fun _ => rfl)
  have hl : Computable (fun a => Encodable.encode (P a).linear) :=
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hf)))))).of_eq (fun _ => rfl)
  have hp := polynomials_family_computable_of_fields P ht hr hc he hz hl
  have htt : Computable (fun a => (P a).types.map Encodable.encode) :=
    list_map_computable_of_code (fun t : LabelType => Encodable.encode t) (fun _ => rfl) (fun a => (P a).types) ht
  have hn := encodingCount_family_computable P htt
  exact ⟨rowList_family_computable P hp,names_family_computable P hn hp,
    pre_question_count_computable P hn hp,pre_distribution_value_computable P hn hp⟩

end Sigma2.CompilerEffective
