import Sigma2.CompilerEffectiveDecoder
noncomputable section
set_option linter.unusedSimpArgs false
namespace Sigma2.CompilerEffectiveCoding
open CompilerSyntaxCodes GameTableEffective

variable {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
@[local fun_prop] theorem peqPred [DecidableEq β] (f g : α → β) (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred (fun a => f a=g a) := Primrec.eq.comp hf hg
@[local fun_prop] theorem peq [DecidableEq β] (f g : α → β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => decide (f a=g a)) := Primrec.eq.decide.comp hf hg
@[local fun_prop] theorem pite (p : α → Prop) [DecidablePred p] (f g : α → β)
    (hp : Primrec (fun a => decide (p a))) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => if p a then f a else g a) :=
  (hp.cond hf hg).of_eq (fun a => by simp only [Bool.cond_decide])
@[local fun_prop] theorem pbind (f : α → Option β) (g : α × β → Option γ)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).bind (fun b => g (a,b))) := Primrec.option_bind hf hg.to₂
attribute [local irreducible] Nat.pair Encodable.encodeList treeCode
attribute [local fun_prop] Primrec Primrec₂ Primrec.id Primrec.const Primrec.fst Primrec.snd
  Primrec.comp Primrec.pair Primrec.succ Primrec.option_some
  Primrec.ite Primrec.eq Primrec.nat_lt Primrec₂.natPair Primrec.unpair

def asNat (n : ℕ) : Option ℕ := if (Nat.unpair n).1=0 then some (Nat.unpair n).2 else none
def asCons (n : ℕ) : Option (ℕ × ℕ) :=
  if (Nat.unpair n).1=0 then none else some ((Nat.unpair n).1-1,(Nat.unpair n).2)
@[simp] theorem asNat_nat (n : ℕ) : asNat (treeCode (treeNat n))=some n := by simp [asNat]
@[simp] theorem asNat_cons (a b : CodecTree) : asNat (treeCode (treeCons a b))=none := by simp [asNat]
@[simp] theorem asCons_nat (n : ℕ) : asCons (treeCode (treeNat n))=none := by simp [asCons]
@[simp] theorem asCons_cons (a b : CodecTree) :
    asCons (treeCode (treeCons a b))=some (treeCode a,treeCode b) := by simp [asCons]

def getUnary (n : ℕ) : Option (ℕ × ℕ) :=
  let tag := CompilerEffective.codeTag n
  let arg := CompilerEffective.codeLeft n
  if n=node tag (cons arg 0) then some (tag,arg) else none

def getBinary (n : ℕ) : Option (ℕ × ℕ × ℕ) :=
  let tag := CompilerEffective.codeTag n
  let p := CompilerEffective.codeLeft n
  let q := CompilerEffective.codeRight n
  if n=node tag (cons p (cons q 0)) then some (tag,p,q) else none
def unaryNorm (n : ℕ) (previous : ℕ → Option ℕ) : Option ℕ := do
  let (tag,arg) ← getUnary n
  if tag=0 then do
    let q ← asNat arg
    let q ← Encodable.decode (α := ℚ) q
    return scalarCode q
  else if tag=1 then do
    let i ← asNat arg
    return labelCode i
  else if tag=4 then do
    let p ← previous arg
    return adjCode p
  else none

def binaryNorm (n : ℕ) (previous : ℕ → Option ℕ) : Option ℕ := do
  let (tag,p,q) ← getBinary n
  if tag=2 ∨ tag=3 then do
    let p ← previous p
    let q ← previous q
    return if tag=2 then addCode p q else mulCode p q
  else none

def exprStep (n : ℕ) (previous : ℕ → Option ℕ) : Option ℕ :=
  (unaryNorm n previous).orElse (fun _ => binaryNorm n previous)

open Lean Elab Tactic Meta in
elab "simpFrozenExpr" : tactic => do
  let some (n,_) := (← getEnv).constants.toList.find? (fun (n,_) =>
    n.eraseMacroScopes.toString.endsWith "instEncodableExpr.encodable_fromS") | throwError "missing frozen decoder"
  let some eqns ← getEqnsFor? n | throwError "missing equations"
  let ids ← eqns.mapM (fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term))
  evalTactic (← `(tactic| simp_all only [exprFromTree, $[$ids],*]))
theorem exprFromTree_equation (s : CodecTree) : exprFromTree s =
    match s with
    | treeCons (treeNat 0) (treeCons (treeNat q) (treeNat 0)) =>
        match Encodable.decode (α := ℚ) q with | some q => some (Expr.scalar q) | _ => none
    | treeCons (treeNat 1) (treeCons (treeNat i) (treeNat 0)) => some (Expr.label i)
    | treeCons (treeNat 2) (treeCons p (treeCons q (treeNat 0))) =>
        match exprFromTree p, exprFromTree q with | some p,some q => some (Expr.add p q) | _,_ => none
    | treeCons (treeNat 3) (treeCons p (treeCons q (treeNat 0))) =>
        match exprFromTree p, exprFromTree q with | some p,some q => some (Expr.mul p q) | _,_ => none
    | treeCons (treeNat 4) (treeCons p (treeNat 0)) => match exprFromTree p with | some p => some (Expr.adj p) | _ => none
    | _ => none := by
  split <;> simpFrozenExpr
  all_goals rfl

@[fun_prop] theorem asNat_primrec : Primrec asNat := by unfold asNat; fun_prop
@[fun_prop] theorem asCons_primrec : Primrec asCons := by unfold asCons; fun_prop
@[fun_prop] theorem pcodeCar : Primrec CompilerEffective.codeCar := by unfold CompilerEffective.codeCar; fun_prop
@[fun_prop] theorem pcodeCdr : Primrec CompilerEffective.codeCdr := by unfold CompilerEffective.codeCdr; fun_prop
@[fun_prop] theorem pcodeTag : Primrec CompilerEffective.codeTag := by unfold CompilerEffective.codeTag; fun_prop
@[fun_prop] theorem pcodeLeft : Primrec CompilerEffective.codeLeft := by unfold CompilerEffective.codeLeft; fun_prop
@[fun_prop] theorem pcodeRight : Primrec CompilerEffective.codeRight := by unfold CompilerEffective.codeRight; fun_prop
@[fun_prop] theorem pcons : Primrec (fun z : ℕ × ℕ => cons z.1 z.2) := by unfold cons; fun_prop
@[fun_prop] theorem pnode : Primrec (fun z : ℕ × ℕ => node z.1 z.2) := by unfold node; fun_prop
@[fun_prop] theorem getUnary_primrec : Primrec getUnary := by unfold getUnary; fun_prop
@[fun_prop] theorem getBinary_primrec : Primrec getBinary := by unfold getBinary; fun_prop

@[simp] theorem pair00 : Nat.pair 0 0=0 := by unfold Nat.pair; decide
@[simp] theorem pair_eq_zero (a b : ℕ) : Nat.pair a b=0 ↔ a=0 ∧ b=0 := by
  calc
    _ ↔ Nat.pair a b=Nat.pair 0 0 := by rw [pair00]
    _ ↔ _ := Nat.pair_eq_pair

theorem getUnary_tree (s : CodecTree) : getUnary (treeCode s) =
    match s with
    | treeCons (treeNat tag) (treeCons arg (treeNat 0)) => some (tag,treeCode arg)
    | _ => none := by
  cases s with
  | nat n => simp [getUnary,CompilerEffective.codeTag,CompilerEffective.codeCar,
      CompilerEffective.codeLeft,CompilerEffective.codeCdr,node,cons]
  | cons h t =>
    cases h with
    | cons a b => simp [getUnary,CompilerEffective.codeTag,CompilerEffective.codeCar,
        CompilerEffective.codeLeft,CompilerEffective.codeCdr,node,cons]
    | nat tag =>
      cases t with
      | nat n => simp [getUnary,CompilerEffective.codeTag,CompilerEffective.codeCar,
          CompilerEffective.codeLeft,CompilerEffective.codeCdr,node,cons]
      | cons arg stop =>
        cases stop with
        | nat n => cases n <;> simp [getUnary,CompilerEffective.codeTag,CompilerEffective.codeCar,
            CompilerEffective.codeLeft,CompilerEffective.codeCdr,node,cons]
        | cons a b => simp [getUnary,CompilerEffective.codeTag,CompilerEffective.codeCar,
            CompilerEffective.codeLeft,CompilerEffective.codeCdr,node,cons]
theorem getBinary_tree (s : CodecTree) : getBinary (treeCode s) =
    match s with
    | treeCons (treeNat tag) (treeCons p (treeCons q (treeNat 0))) =>
        some (tag,treeCode p,treeCode q)
    | _ => none := by
  cases s with
  | nat n => simp [getBinary,CompilerEffective.codeTag,CompilerEffective.codeCar,
      CompilerEffective.codeLeft,CompilerEffective.codeRight,CompilerEffective.codeCdr,node,cons]
  | cons h t =>
    cases h with
    | cons a b => simp [getBinary,CompilerEffective.codeTag,CompilerEffective.codeCar,
        CompilerEffective.codeLeft,CompilerEffective.codeRight,CompilerEffective.codeCdr,node,cons]
    | nat tag =>
      cases t with
      | nat n => simp [getBinary,CompilerEffective.codeTag,CompilerEffective.codeCar,
          CompilerEffective.codeLeft,CompilerEffective.codeRight,CompilerEffective.codeCdr,node,cons]
      | cons p t =>
        cases t with
        | nat n => simp [getBinary,CompilerEffective.codeTag,CompilerEffective.codeCar,
            CompilerEffective.codeLeft,CompilerEffective.codeRight,CompilerEffective.codeCdr,node,cons]
        | cons q stop =>
          cases stop with
          | nat n => cases n <;> simp [getBinary,CompilerEffective.codeTag,CompilerEffective.codeCar,
              CompilerEffective.codeLeft,CompilerEffective.codeRight,CompilerEffective.codeCdr,node,cons]
          | cons a b => simp [getBinary,CompilerEffective.codeTag,CompilerEffective.codeCar,
              CompilerEffective.codeLeft,CompilerEffective.codeRight,CompilerEffective.codeCdr,node,cons]

attribute [-simp] treeCode_nat treeCode_cons

theorem getUnary_tree_some {s : CodecTree} {tag n : ℕ}
    (h : getUnary (treeCode s)=some (tag,n)) :
    ∃ arg, s=treeCons (treeNat tag) (treeCons arg (treeNat 0)) ∧ treeCode arg=n := by
  rw [getUnary_tree] at h
  split at h <;> simp_all

theorem getBinary_tree_some {s : CodecTree} {tag p q : ℕ}
    (h : getBinary (treeCode s)=some (tag,p,q)) :
    ∃ a b, s=treeCons (treeNat tag) (treeCons a (treeCons b (treeNat 0))) ∧
      treeCode a=p ∧ treeCode b=q := by
  rw [getBinary_tree] at h
  split at h <;> simp_all

def exprNorm (n : ℕ) : Option ℕ := (Encodable.decode (α := Expr) n).map Encodable.encode

-- A deliberately symbolic equation: no recursive decoder is reduced here.
theorem exprStep_tree (s : CodecTree) (previous : ℕ → Option ℕ) :
    exprStep (treeCode s) previous =
      match s with
      | treeCons (treeNat 0) (treeCons (treeNat q) (treeNat 0)) =>
          (Encodable.decode (α := ℚ) q).map scalarCode
      | treeCons (treeNat 1) (treeCons (treeNat i) (treeNat 0)) => some (labelCode i)
      | treeCons (treeNat 2) (treeCons p (treeCons q (treeNat 0))) =>
          (previous (treeCode p)).bind (fun p => (previous (treeCode q)).map (addCode p))
      | treeCons (treeNat 3) (treeCons p (treeCons q (treeNat 0))) =>
          (previous (treeCode p)).bind (fun p => (previous (treeCode q)).map (mulCode p))
      | treeCons (treeNat 4) (treeCons p (treeNat 0)) => (previous (treeCode p)).map adjCode
      | _ => none := by
  split
  · simp [exprStep,unaryNorm,binaryNorm,getUnary_tree,getBinary_tree,asNat_nat,Option.map_eq_bind,Function.comp_def]
  · simp [exprStep,unaryNorm,binaryNorm,getUnary_tree,getBinary_tree,asNat_nat,Option.map_eq_bind,Function.comp_def]
  · simp [exprStep,unaryNorm,binaryNorm,getUnary_tree,getBinary_tree,Option.map_eq_bind,Function.comp_def]
  · simp [exprStep,unaryNorm,binaryNorm,getUnary_tree,getBinary_tree,Option.map_eq_bind,Function.comp_def]
  · simp [exprStep,unaryNorm,binaryNorm,getUnary_tree,getBinary_tree,Option.map_eq_bind,Function.comp_def]
  · rename_i h0 h1 h2 h3 h4
    have hu : unaryNorm (treeCode s) previous=none := by
      cases h : getUnary (treeCode s) with
      | none => simp [unaryNorm,h]
      | some z =>
        obtain ⟨arg,hs,ha⟩ := getUnary_tree_some h
        subst s
        obtain ⟨tag,n⟩ := z
        simp only at ha
        subst n
        by_cases ht0 : tag=0
        · subst tag
          cases arg with
          | nat q => exact False.elim (h0 q rfl)
          | cons a b => simp [unaryNorm,getUnary_tree,asNat_cons]
        · by_cases ht1 : tag=1
          · subst tag
            cases arg with
            | nat i => exact False.elim (h1 i rfl)
            | cons a b => simp [unaryNorm,getUnary_tree,ht0,asNat_cons]
          · by_cases ht4 : tag=4
            · subst tag; exact False.elim (h4 arg rfl)
            · simp [unaryNorm,getUnary_tree,ht0,ht1,ht4]
    have hb : binaryNorm (treeCode s) previous=none := by
      cases h : getBinary (treeCode s) with
      | none => simp [binaryNorm,h]
      | some z =>
        obtain ⟨a,b,hs,ha,hb⟩ := getBinary_tree_some h
        subst s
        obtain ⟨tag,p,q⟩ := z
        by_cases ht2 : tag=2
        · subst tag; exact False.elim (h2 a b rfl)
        · by_cases ht3 : tag=3
          · subst tag; exact False.elim (h3 a b rfl)
          · simp [binaryNorm,getBinary_tree,ht2,ht3]
    simp [exprStep,hu,hb]
theorem exprStep_agrees_tree (s : CodecTree) : exprStep (treeCode s) exprNorm=exprNorm (treeCode s) := by
  rw [exprStep_tree]
  conv_rhs => rw [exprNorm,expr_decode_tree,exprFromTree_equation]
  split
  · rename_i q
    cases h : Encodable.decode (α := ℚ) q <;> simp [h]
  · simp
  · rename_i p q
    cases hp : exprFromTree p <;> cases hq : exprFromTree q <;>
      simp [exprNorm,expr_decode_tree,hp,hq]
  · rename_i p q
    cases hp : exprFromTree p <;> cases hq : exprFromTree q <;>
      simp [exprNorm,expr_decode_tree,hp,hq]
  · rename_i p
    cases hp : exprFromTree p <;> simp [exprNorm,expr_decode_tree,hp]
  · simp

theorem exprStep_agrees (n : ℕ) : exprStep n exprNorm=exprNorm n := by
  obtain ⟨s,hs⟩ := treeEquiv.surjective n
  simpa only [treeCode,hs] using exprStep_agrees_tree s
#print axioms exprFromTree_equation
#print axioms exprStep_agrees
end Sigma2.CompilerEffectiveCoding