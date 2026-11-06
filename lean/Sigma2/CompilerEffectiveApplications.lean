import Sigma2.CompilerEffectivePolynomials
/-! Uniform application rows from the frozen original field encodings. -/
noncomputable section
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
namespace Sigma2.CompilerEffective
open CompilerScaffold
attribute [local irreducible] Nat.pair Encodable.encodeList
attribute [local irreducible] structuralPolynomials applicationPolynomials polynomials
  words rowList names graphRows wordRows bindingRows polynomialRow refinementCount
  encodingCount encodingOffset copyAtom blockAtom creation labelCopy expression
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.option_some

variable {α β τ : Type} [Primcodable α] [Primcodable β] [Encodable τ]

/-- A field is decoded using its existing List codec, after an exactly
encoding-preserving change of its internal element view. -/
theorem list_map_computable_of_code (f : τ → β)
    (hf : ∀ t, Encodable.encode (f t)=Encodable.encode t) (xs : α → List τ)
    (hx : Computable (fun a => Encodable.encode (xs a))) :
    Computable (fun a => (xs a).map f) := by
  have hc : Computable (fun a =>
      (Encodable.decode (α := List β) (Encodable.encode (xs a))).getD []) :=
    cgetD _ _ (Primrec.decode.to_comp.comp hx) (Computable.const [])
  exact hc.of_eq (fun a => by
    rw [← PresentationCoding.encode_map f hf (xs a)]
    simp only [Encodable.encodek,Option.getD_some])

abbrev EndData := ℕ × ℕ × ℕ × ℕ
abbrev ZeroData := ℕ × ℕ
abbrev LinearData := ℕ × ℕ × ℕ

def endData (t : Expr × Fin 4 × Fin 4 × Expr) : EndData :=
  (Encodable.encode t.1,t.2.1.val,t.2.2.1.val,Encodable.encode t.2.2.2)
def zeroData (t : Expr × Fin 4) : ZeroData := (Encodable.encode t.1,t.2.val)
def linearData (t : Expr × Fin 4 × Expr) : LinearData :=
  (Encodable.encode t.1,t.2.1.val,Encodable.encode t.2.2)

theorem applicationPolynomials_family_computable (P : α → Presentation)
    (ht : Computable (fun a => (P a).types.map Encodable.encode))
    (hroot : Computable (fun a => (P a).root))
    (hc : Computable (fun a => Encodable.encode (P a).central))
    (hend : Computable (fun a => Encodable.encode (P a).endpoints))
    (hz : Computable (fun a => Encodable.encode (P a).zeros))
    (hl : Computable (fun a => Encodable.encode (P a).linear)) :
    Computable (fun a => applicationPolynomials (P a)) := by
  let A (r : ℕ) (a : α) (i : ℕ) := labelCopy (P a) r i
  let B (r : ℕ) (_ : α) := e r
  let E (r : ℕ) := expansion (A r) (B r)
  have hA (r : ℕ) : Computable₂ (A r) :=
    labelCopy_family_computable (fun z : α × ℕ => P z.1) (fun _ => r) Prod.snd
      (ht.comp Computable.fst) (Computable.const r) Computable.snd
  have hE (r : ℕ) : Computable₂ (E r) := expansion_computable (A r) (B r) (hA r) (Computable.const _)
  have he := encodingCount_family_computable P ht
  have hlabel := labelCopy_family_computable P (fun _ => 4) (fun a => (P a).root)
    ht (Computable.const 4) hroot
  have hcentralCodes : Computable (fun a => (P a).central.map Encodable.encode) :=
    list_map_computable_of_code (fun t : Expr => Encodable.encode t) (fun _ => rfl) (fun a => (P a).central) hc
  have hcentral := expression_list_computable_of_fields P (fun _ => 0) (fun a => (P a).central)
    ht (Computable.const 0) hcentralCodes
  have hends : Computable (fun a => (P a).endpoints.map endData) :=
    list_map_computable_of_code endData (fun _ => rfl) (fun a => (P a).endpoints) hend
  have hzeros : Computable (fun a => (P a).zeros.map zeroData) :=
    list_map_computable_of_code zeroData (fun _ => rfl) (fun a => (P a).zeros) hz
  have hlinear : Computable (fun a => (P a).linear.map (List.map linearData)) :=
    list_map_computable_of_code (List.map linearData)
      (fun row => PresentationCoding.encode_map linearData (fun _ => rfl) row)
      (fun a => (P a).linear) hl
  have hendpoly : Computable (fun a => (P a).endpoints.map (fun t =>
      sub (mul (expression (P a) 4 t.1) (creation (P a) t.2.1.val))
        (mul (creation (P a) t.2.2.1.val) (expression (P a) 0 t.2.2.2)))) := by
    have hnum : Computable (fun a => ((P a).endpoints.map endData).map (fun t =>
        sub (mul (E 4 a t.1) (creation (P a) t.2.1))
          (mul (creation (P a) t.2.2.1) (E 0 a t.2.2.2)))) := by
      have he' : Computable (fun z : α × EndData => encodingCount (P z.1)) := he.comp Computable.fst
      have hp : Computable (fun z : α × EndData => z.2.1) := by fun_prop
      have hi : Computable (fun z : α × EndData => z.2.2.1) := by fun_prop
      have hj : Computable (fun z : α × EndData => z.2.2.2.1) := by fun_prop
      have hq : Computable (fun z : α × EndData => z.2.2.2.2) := by fun_prop
      have hexp4 := (hE 4).comp Computable.fst hp
      have hexp0 := (hE 0).comp Computable.fst hq
      have hiC := ccreation (fun z : α × EndData => P z.1) _ he' hi
      have hjC := ccreation (fun z : α × EndData => P z.1) _ he' hj
      have hterm := cpsub _ _ (cpmul _ _ hexp4 hiC) (cpmul _ _ hjC hexp0)
      exact cmap _ _ hends hterm
    apply hnum.of_eq
    intro a
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro t _
    change sub (mul (expansion _ _ a (Encodable.encode t.1)) _) (mul _
      (expansion _ _ a (Encodable.encode t.2.2.2)))=_
    rw [expansion_agrees P (fun _ => 4) a t.1,expansion_agrees P (fun _ => 0) a t.2.2.2]
    rfl
  have hzeropoly : Computable (fun a => (P a).zeros.map (fun t =>
      mul (expression (P a) 4 t.1) (creation (P a) t.2.val))) := by
    have hnum : Computable (fun a => ((P a).zeros.map zeroData).map (fun t =>
        mul (E 4 a t.1) (creation (P a) t.2))) := by
      have he' : Computable (fun z : α × ZeroData => encodingCount (P z.1)) := he.comp Computable.fst
      have hp : Computable (fun z : α × ZeroData => z.2.1) := by fun_prop
      have hi : Computable (fun z : α × ZeroData => z.2.2) := by fun_prop
      have hexp4 := (hE 4).comp Computable.fst hp
      have hiC := ccreation (fun z : α × ZeroData => P z.1) _ he' hi
      exact cmap _ _ hzeros (cpmul _ _ hexp4 hiC)
    apply hnum.of_eq
    intro a
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro t _
    change mul (expansion _ _ a (Encodable.encode t.1)) _=_
    rw [expansion_agrees P (fun _ => 4) a t.1]
    rfl
  have hlinearpoly : Computable (fun a => (P a).linear.map (fun row =>
      sum (row.map (fun t => mul (mul (expression (P a) 4 t.1)
        (creation (P a) t.2.1.val)) (expression (P a) 0 t.2.2))))) := by
    have hnum : Computable (fun a => ((P a).linear.map (List.map linearData)).map (fun row =>
        sum (row.map (fun t => mul (mul (E 4 a t.1) (creation (P a) t.2.1)) (E 0 a t.2.2))))) := by
      have he' : Computable (fun z : (α × List LinearData) × LinearData => encodingCount (P z.1.1)) :=
        he.comp (Computable.fst.comp Computable.fst)
      have hparam : Computable (fun z : (α × List LinearData) × LinearData => z.1.1) :=
        Computable.fst.comp Computable.fst
      have hp : Computable (fun z : (α × List LinearData) × LinearData => z.2.1) := by fun_prop
      have hi : Computable (fun z : (α × List LinearData) × LinearData => z.2.2.1) := by fun_prop
      have hq : Computable (fun z : (α × List LinearData) × LinearData => z.2.2.2) := by fun_prop
      have hexp4 := (hE 4).comp hparam hp
      have hexp0 := (hE 0).comp hparam hq
      have hiC := ccreation (fun z : (α × List LinearData) × LinearData => P z.1.1) _ he' hi
      have hterm := cpmul _ _ (cpmul _ _ hexp4 hiC) hexp0
      have hinner := cmap (fun z : α × List LinearData => z.2) _ Computable.snd hterm
      exact cmap _ _ hlinear (cpsum _ hinner)
    apply hnum.of_eq
    intro a
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro row _
    apply congrArg sum
    apply List.map_congr_left
    intro t _
    change mul (mul (expansion _ _ a (Encodable.encode t.1)) _) (expansion _ _ a (Encodable.encode t.2.2))=_
    rw [expansion_agrees P (fun _ => 4) a t.1,expansion_agrees P (fun _ => 0) a t.2.2]
    rfl
  have he1 : Computable (fun z : α × ℕ => encodingCount (P z.1)) := he.comp Computable.fst
  have he2 : Computable (fun z : (α × ℕ) × ℕ => encodingCount (P z.1.1)) :=
    he.comp (Computable.fst.comp Computable.fst)
  unfold applicationPolynomials
  fun_prop

/-- All polynomial generation is uniform in the original field codes.
Computability of extracting these fields from the original Presentation decoder
is a separate remaining obligation. -/
theorem polynomials_family_computable_of_fields (P : α → Presentation)
    (ht : Computable (fun a => Encodable.encode (P a).types))
    (hroot : Computable (fun a => (P a).root))
    (hc : Computable (fun a => Encodable.encode (P a).central))
    (hend : Computable (fun a => Encodable.encode (P a).endpoints))
    (hz : Computable (fun a => Encodable.encode (P a).zeros))
    (hl : Computable (fun a => Encodable.encode (P a).linear)) :
    Computable (fun a => polynomials (P a)) := by
  have htt : Computable (fun a => (P a).types.map Encodable.encode) :=
    list_map_computable_of_code (fun t : LabelType => Encodable.encode t) (fun _ => rfl) (fun a => (P a).types) ht
  have hs := structuralPolynomials_family_computable P htt
  have ha := applicationPolynomials_family_computable P htt hroot hc hend hz hl
  exact (capp _ _ hs ha).of_eq (fun a => by simp only [polynomials])

end Sigma2.CompilerEffective
