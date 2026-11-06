import Sigma2.CompilerEffective
open Lean Elab Term in
elab "frozenCodec%" s:str : term => do
  let found := (← getEnv).constants.toList.filter (fun (n,_) =>
    n.eraseMacroScopes.toString.endsWith s.getString)
  match found with
  | [(n,_)] => return mkConst n
  | _ => throwError "expected unique frozen codec constant: {s.getString}, got {found.map Prod.fst}"
namespace Sigma2.CompilerEffectiveCoding
abbrev CodecTree := frozenCodec% ".Mathlib.Deriving.Encodable.S"
abbrev treeEquiv : CodecTree ≃ ℕ := frozenCodec% ".Mathlib.Deriving.Encodable.S_equiv"
abbrev exprFromTree : CodecTree → Option Expr := frozenCodec% "instEncodableExpr.encodable_fromS"
abbrev labelFromTree : CodecTree → Option LabelType := frozenCodec% "instEncodableLabelType.encodable_fromS"
abbrev presentationFromTree : CodecTree → Option Presentation := frozenCodec% "instEncodablePresentation.encodable_fromS"
#print exprFromTree
#print presentationFromTree
@[match_pattern] abbrev treeNat : ℕ → CodecTree := frozenCodec% ".Mathlib.Deriving.Encodable.S.nat"
@[match_pattern] abbrev treeCons : CodecTree → CodecTree → CodecTree := frozenCodec% ".Mathlib.Deriving.Encodable.S.cons"
def treeCode (s : CodecTree) : ℕ := treeEquiv s
@[simp] theorem treeCode_nat (n : ℕ) : treeCode (treeNat n)=Nat.pair 0 n := rfl
@[simp] theorem treeCode_cons (a b : CodecTree) :
    treeCode (treeCons a b)=Nat.pair (treeCode a+1) (treeCode b) := rfl
@[simp] theorem expr_decode_tree (s : CodecTree) :
    Encodable.decode (α := Expr) (treeCode s)=exprFromTree s := by
  change (some (treeEquiv.symm (treeEquiv s))).bind exprFromTree = _
  simp
@[simp] theorem label_decode_tree (s : CodecTree) :
    Encodable.decode (α := LabelType) (treeCode s)=labelFromTree s := by
  change (some (treeEquiv.symm (treeEquiv s))).bind labelFromTree = _
  simp
@[simp] theorem presentation_decode_tree (s : CodecTree) :
    Encodable.decode (α := Presentation) (treeCode s)=presentationFromTree s := by
  change (some (treeEquiv.symm (treeEquiv s))).bind presentationFromTree = _
  simp
#print exprFromTree
open Lean in
run_meta do
  for (n, _) in (← getEnv).constants.toList do
    if n.eraseMacroScopes.toString.endsWith "instEncodableExpr.encodable_fromS" then
      logInfo m!"{(← getConstInfo n).value!}"
end Sigma2.CompilerEffectiveCoding