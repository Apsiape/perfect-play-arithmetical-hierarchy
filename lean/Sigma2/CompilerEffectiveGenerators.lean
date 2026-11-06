import Sigma2.CompilerEffectiveScaffold
/-! Label allocation and recursive expansion from the original encoded type
and expression fields. These lemmas preserve every frozen definition. -/
noncomputable section
set_option maxHeartbeats 250000
set_option linter.unusedSimpArgs false
namespace Sigma2.CompilerEffective
open CompilerScaffold
attribute [local irreducible] Nat.pair Encodable.encodeList
attribute [local irreducible] structuralPolynomials applicationPolynomials polynomials
  words rowList names graphRows wordRows bindingRows polynomialRow refinementCount
  encodingCount encodingOffset copyAtom blockAtom creation labelCopy
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair

variable {α : Type} [Primcodable α]

@[fun_prop] theorem cnatsum (f : α → List ℕ) (hf : Computable f) :
    Computable (fun a => (f a).sum) := by
  have hc := cfoldr f (fun _ => (0:ℕ)) (fun _ z => z.1+z.2) hf (Computable.const 0)
    (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)).to₂
  exact hc.of_eq (fun a => by induction f a <;> simp_all)

def encodedWeight (k : ℕ) : ℕ := if k=Encodable.encode LabelType.contraction then 2 else 1
@[fun_prop] theorem cencodedWeight (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => encodedWeight (f a)) := by unfold encodedWeight; fun_prop
@[simp] theorem encodedWeight_encode (t : LabelType) :
    encodedWeight (Encodable.encode t)=(if t=LabelType.contraction then 2 else 1) := by
  unfold encodedWeight
  simp only [Encodable.encode_injective.eq_iff]

@[simp] theorem label_encode_eq (t u : LabelType) :
    Encodable.encode t=Encodable.encode u ↔ t=u := Encodable.encode_injective.eq_iff

theorem encodingCount_family_computable (P : α → Presentation)
    (ht : Computable (fun a => (P a).types.map Encodable.encode)) :
    Computable (fun a => encodingCount (P a)) := by
  have hc : Computable (fun a => ((P a).types.map Encodable.encode |>.map encodedWeight).sum) := by
    fun_prop
  exact hc.of_eq (fun a => by
    simp only [List.map_map,Function.comp_def,encodedWeight_encode,encodingCount])

theorem encodingOffset_family_computable (P : α → Presentation) (i : α → ℕ)
    (ht : Computable (fun a => (P a).types.map Encodable.encode)) (hi : Computable i) :
    Computable (fun a => encodingOffset (P a) (i a)) := by
  have hc : Computable (fun a =>
      (((P a).types.map Encodable.encode).take (i a) |>.map encodedWeight).sum) := by fun_prop
  exact hc.of_eq (fun a => by
    rw [← List.map_take]
    simp only [List.map_map,Function.comp_def,encodedWeight_encode,encodingOffset])

@[fun_prop] theorem ccorner (i : α → ℕ) (hi : Computable i) :
    Computable (fun a => corner (i a)) := by unfold corner; fun_prop
@[fun_prop] theorem ce (r : α → ℕ) (hr : Computable r) :
    Computable (fun a => e (r a)) := by unfold e; fun_prop
@[fun_prop] theorem cmagic (g : α → ℕ) (hg : Computable g) :
    Computable (fun a => magic (g a)) := by unfold magic; fun_prop
@[fun_prop] theorem cactivity (g : α → ℕ) (hg : Computable g) :
    Computable (fun a => activity (g a)) := by unfold activity; fun_prop
@[fun_prop] theorem caxisParameter (g k : α → ℕ) (hg : Computable g) (hk : Computable k) :
    Computable (fun a => axisParameter (g a) (k a)) := by unfold axisParameter; fun_prop
@[fun_prop] theorem caxis (g k : α → ℕ) (hg : Computable g) (hk : Computable k) :
    Computable (fun a => axis (g a) (k a)) := by unfold axis; fun_prop

@[fun_prop] theorem ccopyAtom (P : α → Presentation) (r l : α → ℕ)
    (he : Computable (fun a => encodingCount (P a))) (hr : Computable r) (hl : Computable l) :
    Computable (fun a => copyAtom (P a) (r a) (l a)) := by unfold copyAtom; fun_prop
@[fun_prop] theorem cblockAtom (P : α → Presentation) (g l : α → ℕ)
    (he : Computable (fun a => encodingCount (P a))) (hg : Computable g) (hl : Computable l) :
    Computable (fun a => blockAtom (P a) (g a) (l a)) := by unfold blockAtom; fun_prop
@[fun_prop] theorem ccreation (P : α → Presentation) (i : α → ℕ)
    (he : Computable (fun a => encodingCount (P a))) (hi : Computable i) :
    Computable (fun a => creation (P a) (i a)) := by unfold creation; fun_prop

theorem labelCopy_family_computable (P : α → Presentation) (r i : α → ℕ)
    (ht : Computable (fun a => (P a).types.map Encodable.encode))
    (hr : Computable r) (hi : Computable i) :
    Computable (fun a => labelCopy (P a) (r a) (i a)) := by
  have he := encodingCount_family_computable P ht
  have ho := encodingOffset_family_computable P i ht hi
  have hu := ccopyAtom P r (fun a => encodingOffset (P a) (i a)) he hr ho
  have hv := ccopyAtom P r (fun a => encodingOffset (P a) (i a)+1) he hr
    (cadd _ _ ho (Computable.const 1))
  have hty : Computable (fun a =>
      ((P a).types.map Encodable.encode)[i a]?.getD (Encodable.encode LabelType.unitary)) := by fun_prop
  have hproj := cscale _ _ (Computable.const (1/2:ℚ)) (capp _ _ (Computable.const one) hu)
  have hpos := cscale _ _ (Computable.const (1/4:ℚ))
    (capp _ _ (capp _ _ (cscalar _ (Computable.const (2:ℚ))) hu) (cpadj _ hu))
  have hcont := cscale _ _ (Computable.const (1/2:ℚ)) (capp _ _ hu hv)
  have hswitch := (ceq _ _ hty (Computable.const (Encodable.encode LabelType.unitary))).cond hu
    ((ceq _ _ hty (Computable.const (Encodable.encode LabelType.projection))).cond hproj
      ((ceq _ _ hty (Computable.const (Encodable.encode LabelType.positive))).cond hpos hcont))
  have hc : Computable (fun a =>
      let u := copyAtom (P a) (r a) (encodingOffset (P a) (i a))
      let v := copyAtom (P a) (r a) (encodingOffset (P a) (i a)+1)
      let k := ((P a).types.map Encodable.encode)[i a]?.getD (Encodable.encode LabelType.unitary)
      mul (e (r a)) (if k=Encodable.encode LabelType.unitary then u
        else if k=Encodable.encode LabelType.projection then scale (1/2) (one++u)
        else if k=Encodable.encode LabelType.positive then scale (1/4) (scalar 2++u++adj u)
        else scale (1/2) (u++v))) :=
    (cpmul _ _ (ce r hr) hswitch).of_eq (fun a => by simp only [Bool.cond_decide])
  apply hc.of_eq
  intro a
  have hcode : ((P a).types.map Encodable.encode)[i a]?.getD (Encodable.encode LabelType.unitary)=
      Encodable.encode ((P a).types[i a]?.getD .unitary) := by
    rw [List.getElem?_map]
    cases (P a).types[i a]? <;> rfl
  dsimp only
  rw [hcode]
  cases hti : (P a).types[i a]? with
  | none => simp [labelCopy,hti]
  | some t => cases t <;> simp [labelCopy,hti]

/-- Uniform recursive expansion, with the original list of Expr codes as input. -/
theorem expression_list_computable_of_fields (P : α → Presentation) (r : α → ℕ)
    (ts : α → List Expr)
    (ht : Computable (fun a => (P a).types.map Encodable.encode))
    (hr : Computable r)
    (hts : Computable (fun a => (ts a).map Encodable.encode)) :
    Computable (fun a => (ts a).map (expression (P a) (r a))) := by
  have hA : Computable (fun z : α × ℕ => labelCopy (P z.1) (r z.1) z.2) :=
    labelCopy_family_computable (fun z : α × ℕ => P z.1) (fun z => r z.1) Prod.snd
      (ht.comp Computable.fst) (hr.comp Computable.fst) Computable.snd
  exact expression_list_computable P r ts hA (ce r hr) hts


theorem count_reindex {β : Type} [Primcodable β]
    (P : α → Presentation) (f : β → α)
    (he : Computable (fun a => encodingCount (P a))) (hf : Computable f) :
    Computable (fun b => encodingCount (P (f b))) := he.comp hf

theorem types_codes_reindex {β : Type} [Primcodable β]
    (P : α → Presentation) (f : β → α)
    (ht : Computable (fun a => (P a).types.map Encodable.encode)) (hf : Computable f) :
    Computable (fun b => (P (f b)).types.map Encodable.encode) := ht.comp hf

end Sigma2.CompilerEffective
