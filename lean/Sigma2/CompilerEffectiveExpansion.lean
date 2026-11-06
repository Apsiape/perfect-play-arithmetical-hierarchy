import Sigma2.CompilerEffectiveFinite
/-! Recursive expansion follows the original derived Expr constructor codes.
The numerical evaluator is identified with the frozen expression on every
encoded Expr; its behavior on other numbers is deliberately immaterial here. -/
noncomputable section
set_option maxHeartbeats 250000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffective
open CompilerScaffold CompilerSyntaxCodes GameTableEffective
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.unpair
  Computable.option_some

def codeCar (n : ℕ) := (Nat.unpair n).1-1
def codeCdr (n : ℕ) := (Nat.unpair n).2
def codeTag (n : ℕ) := (Nat.unpair (codeCar n)).2
def codeData (n : ℕ) := (Nat.unpair (codeCar (codeCdr n))).2
def codeLeft (n : ℕ) := codeCar (codeCdr n)
def codeRight (n : ℕ) := codeCar (codeCdr (codeCdr n))

variable {α : Type} [Primcodable α]
@[fun_prop] theorem ccodeCar (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => codeCar (f a)) := by unfold codeCar; fun_prop
@[fun_prop] theorem ccodeCdr (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => codeCdr (f a)) := by unfold codeCdr; fun_prop
@[fun_prop] theorem ccodeTag (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => codeTag (f a)) := by unfold codeTag; fun_prop
@[fun_prop] theorem ccodeData (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => codeData (f a)) := by unfold codeData; fun_prop
@[fun_prop] theorem ccodeLeft (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => codeLeft (f a)) := by unfold codeLeft; fun_prop
@[fun_prop] theorem ccodeRight (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => codeRight (f a)) := by unfold codeRight; fun_prop

@[fun_prop] theorem crational (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => UpperCoding.rationalCode (f a)) := UpperCoding.rational_decode.to_comp.comp hf

def expansionStep (A : α → ℕ → Poly) (B : α → Poly) (a : α) (n : ℕ)
    (previous : ℕ → Poly) : Poly :=
  if codeTag n=0 then scale (UpperCoding.rationalCode (codeData n)) (B a)
  else if codeTag n=1 then A a (codeData n)
  else if codeTag n=2 then previous (codeLeft n) ++ previous (codeRight n)
  else if codeTag n=3 then mul (previous (codeLeft n)) (previous (codeRight n))
  else if codeTag n=4 then adj (previous (codeLeft n)) else []

def expansion (A : α → ℕ → Poly) (B : α → Poly) (a : α) (n : ℕ) : Poly :=
  expansionStep A B a n (fun k => if h : k<n then expansion A B a k else [])
termination_by n

theorem expansion_computable (A : α → ℕ → Poly) (B : α → Poly)
    (hA : Computable₂ A) (hB : Computable B) : Computable₂ (expansion A B) := by
  have hn : Computable (fun z : α × List Poly => z.2.length) :=
    Computable.list_length.comp Computable.snd
  have ht := ccodeTag _ hn
  have hd := ccodeData _ hn
  have hl : Computable (fun z : α × List Poly => z.2[codeLeft z.2.length]?.getD []) :=
    cgetD _ _ (cget _ _ Computable.snd (ccodeLeft _ hn)) (Computable.const [])
  have hr : Computable (fun z : α × List Poly => z.2[codeRight z.2.length]?.getD []) :=
    cgetD _ _ (cget _ _ Computable.snd (ccodeRight _ hn)) (Computable.const [])
  have hscl := cscale _ _ (crational _ hd) (hB.comp Computable.fst)
  have hlab := hA.comp Computable.fst hd
  have hadd := capp _ _ hl hr
  have hmul := cpmul _ _ hl hr
  have hadj := cpadj _ hl
  have heq (k : ℕ) : Computable (fun z : α × List Poly => decide (codeTag z.2.length=k)) :=
    ceq _ _ ht (Computable.const k)
  have hb := (heq 0).cond hscl ((heq 1).cond hlab ((heq 2).cond hadd
    ((heq 3).cond hmul ((heq 4).cond hadj (Computable.const [])))))
  have hs : Computable (fun z : α × List Poly =>
      some (expansionStep A B z.1 z.2.length (fun k => z.2[k]?.getD []))) :=
    (Computable.option_some.comp hb).of_eq (fun z => by
      simp only [Bool.cond_decide]
      rfl)
  apply Computable.nat_strong_rec (expansion A B) hs.to₂
  intro a n
  simp only [List.length_map,List.length_range]
  have hprev : (fun k => ((List.range n).map (expansion A B a))[k]?.getD []) =
      (fun k => if h : k<n then expansion A B a k else []) := by
    funext k
    by_cases hk : k<n <;> simp [hk]
  rw [hprev]
  conv_rhs => rw [expansion]

lemma cons_left_lt (a b : ℕ) : a<cons a b :=
  lt_of_lt_of_le (Nat.lt_succ_self a) (Nat.left_le_pair _ _)
lemma cons_right_le (a b : ℕ) : b≤cons a b := Nat.right_le_pair _ _
lemma node_right_le (a b : ℕ) : b≤node a b := Nat.right_le_pair _ _
lemma add_left_lt (a b : ℕ) : a<addCode a b :=
  lt_of_lt_of_le (cons_left_lt _ _) (node_right_le _ _)
lemma add_right_lt (a b : ℕ) : b<addCode a b :=
  lt_of_lt_of_le (cons_left_lt _ _)
    (le_trans (cons_right_le _ _) (node_right_le _ _))
lemma mul_left_lt (a b : ℕ) : a<mulCode a b :=
  lt_of_lt_of_le (cons_left_lt _ _) (node_right_le _ _)
lemma mul_right_lt (a b : ℕ) : b<mulCode a b :=
  lt_of_lt_of_le (cons_left_lt _ _)
    (le_trans (cons_right_le _ _) (node_right_le _ _))
lemma adj_left_lt (a : ℕ) : a<adjCode a :=
  lt_of_lt_of_le (cons_left_lt _ _) (node_right_le _ _)
@[simp] theorem codeTag_scalarCode (q : ℚ) : codeTag (scalarCode q)=0 := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeData_scalarCode (q : ℚ) : codeData (scalarCode q)=Encodable.encode q := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeTag_labelCode (i : ℕ) : codeTag (labelCode i)=1 := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeData_labelCode (i : ℕ) : codeData (labelCode i)=i := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeTag_addCode (p q : ℕ) : codeTag (addCode p q)=2 := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeLeft_addCode (p q : ℕ) : codeLeft (addCode p q)=p := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeRight_addCode (p q : ℕ) : codeRight (addCode p q)=q := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeTag_mulCode (p q : ℕ) : codeTag (mulCode p q)=3 := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeLeft_mulCode (p q : ℕ) : codeLeft (mulCode p q)=p := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeRight_mulCode (p q : ℕ) : codeRight (mulCode p q)=q := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeTag_adjCode (p : ℕ) : codeTag (adjCode p)=4 := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]
@[simp] theorem codeLeft_adjCode (p : ℕ) : codeLeft (adjCode p)=p := by
  simp [codeTag,codeData,codeLeft,codeRight,codeCar,codeCdr,scalarCode,labelCode,addCode,mulCode,adjCode,GameTableEffective.node,cons]

/-- Exact agreement with the frozen recursive expansion on the original codes. -/
theorem expansion_agrees (P : α → Presentation) (r : α → ℕ) (a : α) (t : Expr) :
    expansion (fun a i => labelCopy (P a) (r a) i) (fun a => e (r a)) a
      (Encodable.encode t) = expression (P a) (r a) t := by
  induction t with
  | scalar q =>
    change expansion _ _ a (scalarCode q)=_
    rw [expansion]
    simp only [expansionStep,codeTag_scalarCode,ite_true,codeData_scalarCode,
      UpperCoding.rational_encode,expression]
  | label i =>
    change expansion _ _ a (labelCode i)=_
    rw [expansion]
    simp only [expansionStep,codeTag_labelCode,show (1:ℕ)≠0 by decide,ite_false,
      ite_true,codeData_labelCode,expression]
  | add p q ihp ihq =>
    change expansion _ _ a (addCode (Encodable.encode p) (Encodable.encode q))=_
    rw [expansion]
    simp only [expansionStep,codeTag_addCode,codeLeft_addCode,codeRight_addCode]
    simp only [show (2:ℕ)≠0 by decide,show (2:ℕ)≠1 by decide,ite_false,ite_true,dite_true,dite_false,
      add_left_lt,add_right_lt,ihp,ihq,expression]
  | mul p q ihp ihq =>
    change expansion _ _ a (mulCode (Encodable.encode p) (Encodable.encode q))=_
    rw [expansion]
    simp only [expansionStep,codeTag_mulCode,codeLeft_mulCode,codeRight_mulCode]
    simp only [show (3:ℕ)≠0 by decide,show (3:ℕ)≠1 by decide,show (3:ℕ)≠2 by decide,
      ite_false,ite_true,dite_true,dite_false,mul_left_lt,mul_right_lt,ihp,ihq,expression]
  | adj p ihp =>
    change expansion _ _ a (adjCode (Encodable.encode p))=_
    rw [expansion]
    simp only [expansionStep,codeTag_adjCode,codeLeft_adjCode]
    simp only [show (4:ℕ)≠0 by decide,show (4:ℕ)≠1 by decide,show (4:ℕ)≠2 by decide,
      show (4:ℕ)≠3 by decide,ite_false,ite_true,dite_true,dite_false,adj_left_lt,ihp,expression]

theorem expression_list_computable (P : α → Presentation) (r : α → ℕ)
    (ts : α → List Expr)
    (hA : Computable (fun z : α × ℕ => labelCopy (P z.1) (r z.1) z.2))
    (hB : Computable (fun a => e (r a)))
    (hts : Computable (fun a => (ts a).map Encodable.encode)) :
    Computable (fun a => (ts a).map (expression (P a) (r a))) := by
  have hc := cmap (fun a => (ts a).map Encodable.encode)
    (fun z => expansion (fun a i => labelCopy (P a) (r a) i) (fun a => e (r a)) z.1 z.2)
    hts (expansion_computable _ _ hA hB)
  exact hc.of_eq (fun a => by
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro t _
    exact expansion_agrees P r a t)

end Sigma2.CompilerEffective
