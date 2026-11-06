import Sigma2.CompilerEffectiveLabel
noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerSyntaxCodes GameTableEffective CompilerEffective
attribute [local irreducible] Nat.pair Encodable.encodeList treeCode
attribute [local fun_prop] Primrec Primrec₂ Primrec.id Primrec.const Primrec.fst Primrec.snd
  Primrec.comp Primrec.pair Primrec.succ Primrec.option_some Primrec.ite Primrec.unpair
  Primrec.encode peqPred peq pite pcodeCar pcodeCdr pcodeTag pcodeLeft pcodeRight
  presentationCode_primrec
@[local fun_prop] theorem pcodeData : Primrec codeData := by unfold codeData; fun_prop

abbrev PresentationData := List LabelType × ℕ × List ℕ × List Expr ×
  List (Expr × Fin 4 × Fin 4 × Expr) × List (Expr × Fin 4) × List (List (Expr × Fin 4 × Expr))

def dataFields (d : PresentationData) : FieldCodes :=
  (Encodable.encode d.1,d.2.1,Encodable.encode d.2.2.1,Encodable.encode d.2.2.2.1,
    Encodable.encode d.2.2.2.2.1,Encodable.encode d.2.2.2.2.2.1,Encodable.encode d.2.2.2.2.2.2)

def dataPresentation (d : PresentationData) : Presentation :=
  ⟨d.1,d.2.1,d.2.2.1,d.2.2.2.1,d.2.2.2.2.1,d.2.2.2.2.2.1,d.2.2.2.2.2.2⟩

def extractedFields (n : ℕ) : FieldCodes :=
  (codeData n,codeData (codeCdr n),codeData (codeCdr (codeCdr n)),
    codeData (codeCdr (codeCdr (codeCdr n))),
    codeData (codeCdr (codeCdr (codeCdr (codeCdr n)))),
    codeData (codeCdr (codeCdr (codeCdr (codeCdr (codeCdr n))))),
    codeData (codeCdr (codeCdr (codeCdr (codeCdr (codeCdr (codeCdr n)))))))

def getPresentation (n : ℕ) : Option FieldCodes :=
  if n=presentationCode (extractedFields n) then some (extractedFields n) else none

def fieldTree (f : FieldCodes) : CodecTree :=
  treeCons (treeNat 0) (treeCons (treeNat f.1) (treeCons (treeNat f.2.1)
    (treeCons (treeNat f.2.2.1) (treeCons (treeNat f.2.2.2.1)
    (treeCons (treeNat f.2.2.2.2.1) (treeCons (treeNat f.2.2.2.2.2.1)
    (treeCons (treeNat f.2.2.2.2.2.2) (treeNat 0))))))))

theorem treeCode_fieldTree (f : FieldCodes) : treeCode (fieldTree f)=presentationCode f := by
  simp [fieldTree,treeCode_cons,treeCode_nat,presentationCode,node]

theorem extractedFields_code (f : FieldCodes) : extractedFields (presentationCode f)=f := by
  simp [extractedFields,presentationCode,node,codeData,codeCar,codeCdr]

theorem getPresentation_tree (s : CodecTree) : getPresentation (treeCode s) =
    match s with
    | treeCons (treeNat 0) (treeCons (treeNat a) (treeCons (treeNat b) (treeCons (treeNat c)
        (treeCons (treeNat d) (treeCons (treeNat e) (treeCons (treeNat f)
        (treeCons (treeNat g) (treeNat 0)))))))) => some (a,b,c,d,e,f,g)
    | _ => none := by
  split
  · rename_i a b c d e f g
    change getPresentation (treeCode (fieldTree (a,b,c,d,e,f,g)))=some (a,b,c,d,e,f,g)
    rw [treeCode_fieldTree]
    simp [getPresentation,extractedFields_code]
  · rename_i h
    dsimp only [getPresentation]
    split
    next he =>
      have hs : s=fieldTree (extractedFields (treeCode s)) :=
        treeCode_injective (he.trans (treeCode_fieldTree _).symm)
      exact False.elim (h _ _ _ _ _ _ _ hs)
    next _ => rfl

open Lean Elab Tactic Meta in
elab "simpFrozenPresentation" : tactic => do
  let some (n,_) := (← getEnv).constants.toList.find? (fun (n,_) =>
    n.eraseMacroScopes.toString.endsWith "instEncodablePresentation.encodable_fromS") | throwError "missing frozen decoder"
  let some eqns ← getEqnsFor? n | throwError "missing equations"
  let ids ← eqns.mapM (fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term))
  evalTactic (← `(tactic| simp_all only [presentationFromTree, $[$ids],*]))

theorem presentationFromTree_equation (s : CodecTree) : presentationFromTree s =
    match s with
    | treeCons (treeNat 0) (treeCons (treeNat a) (treeCons (treeNat b) (treeCons (treeNat c)
        (treeCons (treeNat d) (treeCons (treeNat e) (treeCons (treeNat f)
        (treeCons (treeNat g) (treeNat 0)))))))) =>
      match Encodable.decode (α := List LabelType) a, Encodable.decode (α := ℕ) b, Encodable.decode (α := List ℕ) c,
        Encodable.decode (α := List Expr) d, Encodable.decode (α := List (Expr × Fin 4 × Fin 4 × Expr)) e,
        Encodable.decode (α := List (Expr × Fin 4)) f,
        Encodable.decode (α := List (List (Expr × Fin 4 × Expr))) g with
      | some a,some b,some c,some d,some e,some f,some g => some ⟨a,b,c,d,e,f,g⟩
      | _,_,_,_,_,_,_ => none
    | _ => none := by
  split <;> simpFrozenPresentation
  all_goals rfl

def decodeData (f : FieldCodes) : Option PresentationData :=
  Encodable.decode (α := PresentationData) (Encodable.encode f)

def presentationNorm (n : ℕ) : Option ℕ :=
  ((getPresentation n).bind decodeData).map (fun d => presentationCode (dataFields d))

@[local fun_prop] theorem extractedFields_primrec : Primrec extractedFields := by unfold extractedFields; fun_prop
@[local fun_prop] theorem getPresentation_primrec : Primrec getPresentation := by unfold getPresentation; fun_prop
@[local fun_prop] theorem dataFields_primrec : Primrec dataFields := by unfold dataFields; fun_prop
@[local fun_prop] theorem decodeData_primrec : Primrec decodeData := Primrec.decode.comp Primrec.encode

theorem presentationNorm_primrec : Primrec presentationNorm :=
  (Primrec.option_map₁ (presentationCode_primrec.comp dataFields_primrec)).comp
    ((Primrec.option_bind₁ decodeData_primrec).comp getPresentation_primrec)

theorem presentationNorm_agrees_tree (s : CodecTree) :
    presentationNorm (treeCode s)=(Encodable.decode (α := Presentation) (treeCode s)).map Encodable.encode := by
  rw [presentation_decode_tree,presentationFromTree_equation]
  unfold presentationNorm
  rw [getPresentation_tree]
  split
  · rename_i a b c d e f g
    simp only [Option.bind_some]
    unfold decodeData
    simp only [PresentationCoding.encode_prod,Encodable.decode_prod_val,Nat.unpair_pair,
      Encodable.decode_nat,Encodable.encode_nat,Option.bind_some]
    cases ha : Encodable.decode (α := List LabelType) a <;>
    cases hc : Encodable.decode (α := List ℕ) c <;>
    cases hd : Encodable.decode (α := List Expr) d <;>
    cases he : Encodable.decode (α := List (Expr × Fin 4 × Fin 4 × Expr)) e <;>
    cases hf : Encodable.decode (α := List (Expr × Fin 4)) f <;>
    cases hg : Encodable.decode (α := List (List (Expr × Fin 4 × Expr))) g <;>
      simp only [ha,hc,hd,he,hf,hg,Option.bind_none,Option.bind_some,Option.map_none,Option.map_some]
    apply congrArg some
    rename_i ta tc td te tf tg
    exact presentationCode_eq_encode ⟨ta,b,tc,td,te,tf,tg⟩
  · simp

theorem presentationNorm_agrees (n : ℕ) :
    presentationNorm n=(Encodable.decode (α := Presentation) n).map Encodable.encode := by
  obtain ⟨s,hs⟩ := treeEquiv.surjective n
  simpa only [treeCode,hs] using presentationNorm_agrees_tree s

instance presentationPrimcodable : Primcodable Presentation where
  toEncodable := Sigma2.instEncodablePresentation
  prim := (Primrec.nat_iff.mp (Primrec.encode.comp presentationNorm_primrec)).of_eq (fun n => by
    rw [presentationNorm_agrees]
    cases Encodable.decode (α := Presentation) n <;> rfl)

theorem fields_primrec : Primrec CompilerSyntaxCodes.fields :=
  (extractedFields_primrec.comp Primrec.encode).of_eq (fun P => by
    rw [← presentationCode_eq_encode P,extractedFields_code])

def emptyPresentation : Presentation := ⟨[],0,[],[],[],[],[]⟩
def decodedPresentation (n : ℕ) : Presentation :=
  (Encodable.decode (α := Presentation) n).getD emptyPresentation

theorem presentation_decoder_computable : Computable (Encodable.decode (α := Presentation)) := Primrec.decode.to_comp
theorem presentation_validity_computable :
    Computable (fun n => (Encodable.decode (α := Presentation) n).isSome) :=
  Primrec.option_isSome.to_comp.comp presentation_decoder_computable

theorem decoded_fields_computable : Computable (fun n => CompilerSyntaxCodes.fields (decodedPresentation n)) :=
  fields_primrec.to_comp.comp (Primrec.option_getD.to_comp.comp presentation_decoder_computable (Computable.const emptyPresentation))

theorem decoded_finite_traversals :
    Computable (fun n => CompilerScaffold.rowList (decodedPresentation n)) ∧
    Computable (fun n => CompilerScaffold.names (decodedPresentation n)) ∧
    Computable (fun n => (CompilerScaffold.scenario (decodedPresentation n)).questionsA) ∧
    Computable (fun n => (1:ℚ) /
      (((CompilerScaffold.scenario (decodedPresentation n)).questionsA+1)*
       ((CompilerScaffold.scenario (decodedPresentation n)).questionsB+1) : ℕ)) :=
  CompilerEffective.finite_traversals_from_original_fields decodedPresentation decoded_fields_computable

#print axioms presentationFromTree_equation
#print axioms presentationNorm_primrec
#print axioms presentationPrimcodable
#print axioms presentation_validity_computable
#print axioms decoded_fields_computable
#print axioms decoded_finite_traversals
end Sigma2.CompilerEffectiveCoding