import Sigma2.CompilerEffectiveExprPrim
noncomputable section
set_option maxHeartbeats 150000
set_option linter.unusedSimpArgs false
namespace Sigma2.CompilerEffectiveCoding
open CompilerEffective
attribute [local irreducible] Nat.pair Encodable.encodeList Compiler.cellSign Compiler.retained Compiler.fmsRule Compiler.conditionalFmsRule
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.cond Computable.succ
variable {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]

lemma bool_decide_and (p q : Prop) [Decidable p] [Decidable q] :
    decide (p ∧ q)=(decide p && decide q) := by by_cases p <;> by_cases q <;> simp_all
lemma bool_decide_or (p q : Prop) [Decidable p] [Decidable q] :
    decide (p ∨ q)=(decide p || decide q) := by by_cases p <;> by_cases q <;> simp_all

lemma bool_decide_iff (p q : Prop) [Decidable p] [Decidable q] :
    decide (p ↔ q)=decide (decide p=decide q) := by by_cases p <;> by_cases q <;> simp_all

@[fun_prop] theorem csucc (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => Nat.succ (f a)) := Computable.succ.comp hf

@[fun_prop] theorem cor (f g : α → Bool) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a || g a) := Primrec.or.to_comp.comp hf hg
@[fun_prop] theorem cxor (f g : α → Bool) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => Bool.xor (f a) (g a)) := (Primrec.dom_bool₂ Bool.xor).to_comp.comp hf hg
@[fun_prop] theorem cle (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => decide (f a≤g a)) := Primrec.nat_le.decide.to_comp.comp hf hg
theorem cdecideAnd (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp : Computable (fun a => decide (p a))) (hq : Computable (fun a => decide (q a))) :
    Computable (fun a => decide (p a ∧ q a)) := by
  exact (cand _ _ hp hq).of_eq (fun a => by simp)
theorem cdecideOr (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp : Computable (fun a => decide (p a))) (hq : Computable (fun a => decide (q a))) :
    Computable (fun a => decide (p a ∨ q a)) := by
  exact (cor _ _ hp hq).of_eq (fun a => by simp)
theorem cdecideNot (p : α → Prop) [DecidablePred p]
    (hp : Computable (fun a => decide (p a))) :
    Computable (fun a => decide (¬p a)) := by
  exact (cnot _ hp).of_eq (fun a => by simp)
theorem cdecideIff (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hp : Computable (fun a => decide (p a))) (hq : Computable (fun a => decide (q a))) :
    Computable (fun a => decide (p a ↔ q a)) := by
  exact (ceq _ _ hp hq).of_eq (fun a => by
    by_cases hh : p a <;> by_cases hk : q a <;> simp [hh,hk])

@[fun_prop] theorem call (f : α → List β) (p : α × β → Bool)
    (hf : Computable f) (hp : Computable p) :
    Computable (fun a => (f a).all (fun b => p (a,b))) := by
  have hc := cfoldr f (fun _ => true) (fun a z => p (a,z.1) && z.2) hf (Computable.const true)
    (cand _ _ (hp.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)).to₂
  exact hc.of_eq (fun a => by induction f a <;> simp_all)

@[fun_prop] theorem cNatPow (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a ^ g a) := (Primrec₂.unpaired'.mp Nat.Primrec.pow).to_comp.comp hf hg

theorem cellSign_computable : Computable (fun z : Bool × ℕ × ℕ => Compiler.cellSign z.1 z.2.1 z.2.2) := by
  unfold Compiler.cellSign
  fun_prop
@[fun_prop] theorem ccellSign (p : α → Bool) (v j : α → ℕ)
    (hp : Computable p) (hv : Computable v) (hj : Computable j) :
    Computable (fun a => Compiler.cellSign (p a) (v a) (j a)) :=
  cellSign_computable.comp (hp.pair (hv.pair hj))

theorem retained_computable : Computable (fun z : ℕ × ℕ => Compiler.retained z.1 z.2) := by
  unfold Compiler.retained
  fun_prop
@[fun_prop] theorem cretained (x k : α → ℕ) (hx : Computable x) (hk : Computable k) :
    Computable (fun a => Compiler.retained (x a) (k a)) := retained_computable.comp (hx.pair hk)

theorem fmsRule_computable : Computable (fun z : ℕ × ℕ × ℕ × ℕ =>
    Compiler.fmsRule z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hx : Computable (fun z : ℕ × ℕ × ℕ × ℕ => z.1) := Computable.fst
  have hy : Computable (fun z : ℕ × ℕ × ℕ × ℕ => z.2.1) := Computable.fst.comp Computable.snd
  have ha : Computable (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hb : Computable (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ha0 := ceq _ _ ha (Computable.const 0)
  have hb0 := ceq _ _ hb (Computable.const 0)
  have hx0 := ceq _ _ hx (Computable.const 0)
  have hy0 := ceq _ _ hy (Computable.const 0)
  have hsignA := ccellSign _ _ _ (Computable.const false) (csub _ _ ha (Computable.const 1)) hy
  have hsignB := ccellSign _ _ _ (ceq _ _ hy (Computable.const 2)) (csub _ _ hb (Computable.const 1)) hx
  have hflag := (cor _ _ ha0 hb0).cond (cand _ _ ha0 hb0) (ceq _ _ hsignA hsignB)
  have hretX := cretained _ _ (csub _ _ hx (Computable.const 3)) (csub _ _ ha (Computable.const 2))
  have hretY := cretained _ _ (csub _ _ hy (Computable.const 3)) (csub _ _ hb (Computable.const 2))
  have hmarginX := (clt _ _ ha (Computable.const 2)).cond
    (cor _ _ hb0 (ceq _ _ hb (csub _ _ hx (Computable.const 2))))
    (ceq _ _ hb (cadd _ _ hretX (Computable.const 1)))
  have hmarginY := (clt _ _ hb (Computable.const 2)).cond
    (cor _ _ ha0 (ceq _ _ ha (csub _ _ hy (Computable.const 2))))
    (ceq _ _ ha (cadd _ _ hretY (Computable.const 1)))
  have hparity := ceq _ _ (cmod _ _ (cadd _ _ ha hb) (Computable.const 2))
    (cmod _ _ (cmul _ _ (csub _ _ hx (Computable.const 3)) (csub _ _ hy (Computable.const 3))) (Computable.const 2))
  have hlast := (cand _ _ (cle _ _ (Computable.const 3) hx)
    (cand _ _ (cle _ _ (Computable.const 3) hy)
      (cand _ _ (clt _ _ ha (Computable.const 2)) (clt _ _ hb (Computable.const 2))))).cond hparity (Computable.const true)
  have hc := (cand _ _ (clt _ _ hx (Computable.const 3)) (clt _ _ hy (Computable.const 3))).cond hflag
    ((cand _ _ (cle _ _ (Computable.const 3) hx) hy0).cond hmarginX
      ((cand _ _ hx0 (cle _ _ (Computable.const 3) hy)).cond hmarginY hlast))
  apply hc.of_eq
  intro z
  unfold Compiler.fmsRule
  simp only [← bool_decide_and,← bool_decide_or,Bool.cond_decide]
@[fun_prop] theorem cfmsRule (x y a b : α → ℕ)
    (hx : Computable x) (hy : Computable y) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => Compiler.fmsRule (x z) (y z) (a z) (b z)) :=
  fmsRule_computable.comp (hx.pair (hy.pair (ha.pair hb)))

theorem conditionalFmsRule_computable : Computable (fun z : ℕ × ℕ × ℕ × ℕ =>
    Compiler.conditionalFmsRule z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have ha : Computable (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hb : Computable (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have ha5 := ceq _ _ ha (Computable.const 5)
  have hb5 := ceq _ _ hb (Computable.const 5)
  apply ((cor _ _ ha5 hb5).cond (cand _ _ ha5 hb5) fmsRule_computable).of_eq
  intro z
  unfold Compiler.conditionalFmsRule
  simp only [← bool_decide_and,← bool_decide_or,Bool.cond_decide]
@[fun_prop] theorem cconditionalFmsRule (x y a b : α → ℕ)
    (hx : Computable x) (hy : Computable y) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => Compiler.conditionalFmsRule (x z) (y z) (a z) (b z)) :=
  conditionalFmsRule_computable.comp (hx.pair (hy.pair (ha.pair hb)))

#print axioms cellSign_computable
#print axioms fmsRule_computable
#print axioms conditionalFmsRule_computable
end Sigma2.CompilerEffectiveCoding