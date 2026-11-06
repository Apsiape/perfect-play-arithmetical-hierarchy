import Sigma2.CompilerEffectiveGenerators
/-! Uniform structural polynomial generation from the original type field. -/
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
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.option_some


variable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]

@[fun_prop] theorem clist_filterMap (f : α → List β) (g : α → β → Option σ)
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).filterMap (g a)) := by
  have hopt : Computable (fun z : α × β => (g z.1 z.2).toList) := by
    have hc := Computable.option_casesOn hg (Computable.const ([] : List σ))
      (Computable.list_cons.comp Computable.snd (Computable.const [])).to₂
    exact hc.of_eq (fun z => by cases g z.1 z.2 <;> rfl)
  have hc := clist_flatMap f (fun a b => (g a b).toList) hf hopt
  exact hc.of_eq (fun a => by
    induction f a with
    | nil => rfl
    | cons b l ih => cases hgb : g a b <;> simp [hgb,ih,List.filterMap_cons])

@[fun_prop] theorem types_length_family_computable (P : α → Presentation)
    (ht : Computable (fun a => (P a).types.map Encodable.encode)) :
    Computable (fun a => (P a).types.length) :=
  (clen _ ht).of_eq (fun a => by simp)

@[fun_prop] theorem cprojectionAt (P : α → Presentation) (i : α → ℕ)
    (ht : Computable (fun a => (P a).types.map Encodable.encode)) (hi : Computable i) :
    Computable (fun a => decide ((P a).types[i a]?=some LabelType.projection)) := by
  have hc := ceq (fun a => ((P a).types.map Encodable.encode)[i a]?)
    (fun _ => some (Encodable.encode LabelType.projection))
    (cget _ _ ht hi) (Computable.const _)
  apply hc.of_eq
  intro a
  simp only [List.getElem?_map]
  cases (P a).types[i a]? <;> simp

@[fun_prop] theorem ctransportTerm (P : α → Presentation) (g l k : α → ℕ)
    (he : Computable (fun a => encodingCount (P a)))
    (hg : Computable g) (hl : Computable l) (hk : Computable k) :
    Computable (fun a => transportTerm (P a) (g a) (l a) (k a)) := by
  have hx : Computable (fun a => if k a/2=0 then one else axis (g a) 0) := by fun_prop
  have hz : Computable (fun a => if k a%2=0 then one else axis (g a) 1) := by fun_prop
  have ht := cpmul _ _ hx hz
  have hg1 := cadd _ _ hg (Computable.const 1)
  have hu := ccopyAtom P (fun a => g a+1) l he hg1 hl
  have he1 := ce (fun a => g a+1) hg1
  exact (cpmul _ _ (cpmul _ _ ht (cpmul _ _ he1 hu)) (cpadj _ ht)).of_eq (fun a => rfl)

private def fixedStructural : List Poly :=
  [sub (sum ((List.range 17).map corner)) one] ++
  (List.range 25).map (fun i => sub (mul (atom i) (atom i)) one) ++
  (List.range 4).flatMap (fun g => (List.range 2).map (fun k =>
    sub (axis g k) (one ++ scale (-2) (magic g) ++ scale 2 (axisParameter g k))))
attribute [local irreducible] fixedStructural

theorem structuralPolynomials_family_computable (P : α → Presentation)
    (ht : Computable (fun a => (P a).types.map Encodable.encode)) :
    Computable (fun a => structuralPolynomials (P a)) := by
  have he := encodingCount_family_computable P ht
  have hl := types_length_family_computable P ht
  have hcopyTerm : Computable (fun z : (α × ℕ) × ℕ =>
      mul (sub (copyAtom (P z.1.1) z.1.2 z.2) one) (sub one (e z.1.2))) := by
    have hu := ccopyAtom (fun z : (α × ℕ) × ℕ => P z.1.1)
      (fun z => z.1.2) Prod.snd (he.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst) Computable.snd
    exact cpmul _ _ (cpsub _ _ hu (Computable.const one))
      (cpsub _ _ (Computable.const one) (ce _ (Computable.snd.comp Computable.fst)))
  have hcopyInner : Computable (fun z : α × ℕ =>
      (List.range (encodingCount (P z.1))).map (fun l =>
        mul (sub (copyAtom (P z.1) z.2 l) one) (sub one (e z.2)))) :=
    cmap _ _ (crange _ (he.comp Computable.fst)) hcopyTerm
  have hcopy : Computable (fun a => (List.range 5).flatMap (fun r =>
      (List.range (encodingCount (P a))).map (fun l =>
        mul (sub (copyAtom (P a) r l) one) (sub one (e r))))) :=
    cflat _ _ (Computable.const _) hcopyInner
  have hprojTerm : Computable (fun z : (α × ℕ) × ℕ =>
      if (P z.1.1).types[z.2]?=some LabelType.projection then
        some (sub (mul (copyAtom (P z.1.1) z.1.2 (encodingOffset (P z.1.1) z.2))
          (copyAtom (P z.1.1) z.1.2 (encodingOffset (P z.1.1) z.2))) one) else none) := by
    have ht' : Computable (fun z : (α × ℕ) × ℕ => (P z.1.1).types.map Encodable.encode) :=
      ht.comp (Computable.fst.comp Computable.fst)
    have ho := encodingOffset_family_computable (fun z : (α × ℕ) × ℕ => P z.1.1) Prod.snd ht' Computable.snd
    have hu := ccopyAtom (fun z : (α × ℕ) × ℕ => P z.1.1)
      (fun z => z.1.2) _ (he.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst) ho
    have hb := cpsub _ _ (cpmul _ _ hu hu) (Computable.const one)
    have hp := cprojectionAt (fun z : (α × ℕ) × ℕ => P z.1.1) Prod.snd ht' Computable.snd
    exact (hp.cond (Computable.option_some.comp hb) (Computable.const none)).of_eq
      (fun z => by simp only [Bool.cond_decide])
  have hprojInner : Computable (fun z : α × ℕ =>
      (List.range (P z.1).types.length).filterMap (fun i =>
        if (P z.1).types[i]?=some LabelType.projection then
          some (sub (mul (copyAtom (P z.1) z.2 (encodingOffset (P z.1) i))
            (copyAtom (P z.1) z.2 (encodingOffset (P z.1) i))) one) else none)) :=
    clist_filterMap _ _ (crange _ (hl.comp Computable.fst)) hprojTerm
  have hprojection : Computable (fun a => (List.range 5).flatMap (fun r =>
      (List.range (P a).types.length).filterMap (fun i =>
        if (P a).types[i]?=some LabelType.projection then
          some (sub (mul (copyAtom (P a) r (encodingOffset (P a) i))
            (copyAtom (P a) r (encodingOffset (P a) i))) one) else none))) :=
    cflat _ _ (Computable.const _) hprojInner
  have htterm : Computable (fun z : ((α × ℕ) × ℕ) × ℕ =>
      transportTerm (P z.1.1.1) z.1.1.2 z.1.2 z.2) :=
    ctransportTerm _ _ _ _ (he.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      (Computable.snd.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst) Computable.snd
  have htmap : Computable (fun z : (α × ℕ) × ℕ =>
      (List.range 4).map (transportTerm (P z.1.1) z.1.2 z.2)) :=
    cmap _ _ (Computable.const _) htterm
  have hblockTerm : Computable (fun z : (α × ℕ) × ℕ =>
      sub (blockAtom (P z.1.1) z.1.2 z.2) (sub one (activity z.1.2) ++
        mul (e z.1.2) (copyAtom (P z.1.1) z.1.2 z.2) ++
        sum ((List.range 4).map (transportTerm (P z.1.1) z.1.2 z.2)))) := by
    have he' : Computable (fun z : (α × ℕ) × ℕ => encodingCount (P z.1.1)) :=
      he.comp (Computable.fst.comp Computable.fst)
    have hg' := Computable.snd.comp (Computable.fst : Computable (Prod.fst : ((α × ℕ) × ℕ) → α × ℕ))
    have hu := ccopyAtom _ _ _ he' hg' Computable.snd
    have hb := cblockAtom _ _ _ he' hg' Computable.snd
    have hs1 := cpsub _ _ (Computable.const one) (cactivity _ hg')
    have hs2 := cpmul _ _ (ce _ hg') hu
    exact cpsub _ _ hb (capp _ _ (capp _ _ hs1 hs2) (cpsum _ htmap))
  have hblockInner : Computable (fun z : α × ℕ =>
      (List.range (encodingCount (P z.1))).map (fun l =>
        sub (blockAtom (P z.1) z.2 l) (sub one (activity z.2) ++
          mul (e z.2) (copyAtom (P z.1) z.2 l) ++
          sum ((List.range 4).map (transportTerm (P z.1) z.2 l))))) :=
    cmap _ _ (crange _ (he.comp Computable.fst)) hblockTerm
  have hblocks : Computable (fun a => (List.range 4).flatMap (fun g =>
      (List.range (encodingCount (P a))).map (fun l =>
        sub (blockAtom (P a) g l) (sub one (activity g) ++
          mul (e g) (copyAtom (P a) g l) ++
          sum ((List.range 4).map (transportTerm (P a) g l)))))) :=
    cflat _ _ (Computable.const _) hblockInner
  have hcreationTerm : Computable (fun z : α × ℕ =>
      sub (creation (P z.1) z.2) (mul (mul (e 4) (creation (P z.1) z.2)) (e 0))) := by
    have hu := ccreation (fun z : α × ℕ => P z.1) Prod.snd (he.comp Computable.fst) Computable.snd
    exact cpsub _ _ hu (cpmul _ _ (cpmul _ _ (Computable.const (e 4)) hu) (Computable.const (e 0)))
  have hcreations : Computable (fun a => (List.range 4).map (fun i =>
      sub (creation (P a) i) (mul (mul (e 4) (creation (P a) i)) (e 0)))) :=
    cmap _ _ (Computable.const _) hcreationTerm
  have hs := capp _ _ (Computable.const fixedStructural)
    (capp _ _ hcopy (capp _ _ hprojection (capp _ _ hblocks hcreations)))
  exact hs.of_eq (fun a => by
    simp only [fixedStructural,structuralPolynomials,List.append_assoc])

end Sigma2.CompilerEffective
