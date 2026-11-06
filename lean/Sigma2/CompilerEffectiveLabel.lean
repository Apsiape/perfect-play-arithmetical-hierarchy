import Sigma2.CompilerEffectiveExprPrim
noncomputable section
set_option linter.unusedSimpArgs false
namespace Sigma2.CompilerEffectiveCoding
open CompilerSyntaxCodes GameTableEffective
attribute [local irreducible] Nat.pair Encodable.encodeList treeCode
attribute [local fun_prop] Primrec Primrec₂ Primrec.id Primrec.const Primrec.fst Primrec.snd
  Primrec.comp Primrec.pair Primrec.succ Primrec.option_some Primrec.ite Primrec.unpair
  typeCode_primrec peqPred peq pite

open Lean Elab Tactic Meta in
elab "simpFrozenLabel" : tactic => do
  let some (n,_) := (← getEnv).constants.toList.find? (fun (n,_) =>
    n.eraseMacroScopes.toString.endsWith "instEncodableLabelType.encodable_fromS") | throwError "missing frozen decoder"
  let some eqns ← getEqnsFor? n | throwError "missing equations"
  let ids ← eqns.mapM (fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term))
  evalTactic (← `(tactic| simp_all only [labelFromTree, $[$ids],*]))

theorem labelFromTree_equation (s : CodecTree) : labelFromTree s =
    match s with
    | treeCons (treeNat 0) (treeNat 0) => some LabelType.unitary
    | treeCons (treeNat 1) (treeNat 0) => some LabelType.projection
    | treeCons (treeNat 2) (treeNat 0) => some LabelType.positive
    | treeCons (treeNat 3) (treeNat 0) => some LabelType.contraction
    | _ => none := by
  split <;> simpFrozenLabel

theorem treeCode_injective : Function.Injective treeCode := by
  intro a b h
  unfold treeCode at h
  exact treeEquiv.injective h

@[simp] theorem typeCode_inj (a b : ℕ) : typeCode a=typeCode b ↔ a=b := by
  simp [typeCode,node]

theorem treeCode_type (tag : ℕ) : treeCode (treeCons (treeNat tag) (treeNat 0))=typeCode tag := by
  simp [treeCode_cons,treeCode_nat,typeCode,node]

def labelNorm (n : ℕ) : Option ℕ :=
  if n=typeCode 0 then some (typeCode 0)
  else if n=typeCode 1 then some (typeCode 1)
  else if n=typeCode 2 then some (typeCode 2)
  else if n=typeCode 3 then some (typeCode 3)
  else none

theorem labelNorm_primrec : Primrec labelNorm := by unfold labelNorm; fun_prop

theorem labelNorm_agrees_tree (s : CodecTree) :
    labelNorm (treeCode s)=(Encodable.decode (α := LabelType) (treeCode s)).map Encodable.encode := by
  rw [label_decode_tree,labelFromTree_equation]
  split
  · rw [treeCode_type]; simpa [labelNorm] using congrArg some typeCode_encode.1
  · rw [treeCode_type]; simpa [labelNorm] using congrArg some typeCode_encode.2.1
  · rw [treeCode_type]; simpa [labelNorm] using congrArg some typeCode_encode.2.2.1
  · rw [treeCode_type]; simpa [labelNorm] using congrArg some typeCode_encode.2.2.2
  · rename_i h0 h1 h2 h3
    have hn (tag : ℕ) (h : s≠treeCons (treeNat tag) (treeNat 0)) : treeCode s≠typeCode tag := by
      intro he
      apply h
      exact treeCode_injective (he.trans (treeCode_type tag).symm)
    simp [labelNorm,hn 0 h0,hn 1 h1,hn 2 h2,hn 3 h3]

theorem labelNorm_agrees (n : ℕ) :
    labelNorm n=(Encodable.decode (α := LabelType) n).map Encodable.encode := by
  obtain ⟨s,hs⟩ := treeEquiv.surjective n
  simpa only [treeCode,hs] using labelNorm_agrees_tree s

instance labelPrimcodable : Primcodable LabelType where
  toEncodable := Sigma2.instEncodableLabelType
  prim := (Primrec.nat_iff.mp (Primrec.encode.comp labelNorm_primrec)).of_eq (fun n => by
    rw [labelNorm_agrees]
    cases Encodable.decode (α := LabelType) n <;> rfl)

theorem label_decoder_computable : Computable (Encodable.decode (α := LabelType)) := Primrec.decode.to_comp
#print axioms labelFromTree_equation
#print axioms labelPrimcodable
#print axioms label_decoder_computable
end Sigma2.CompilerEffectiveCoding