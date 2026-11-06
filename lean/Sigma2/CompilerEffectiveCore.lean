import Sigma2.CompilerScaffold
import Sigma2.PresentationCoding
import Sigma2.SimulatorParameterCoding

/-! Effective finite traversals. All conclusions concern the supplied functions. -/
noncomputable section
namespace Sigma2.CompilerEffective
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair
  Computable.option_some Computable.option_casesOn Computable.option_map
  Computable.option_bind Computable.cond

variable {α β γ σ : Type} [Primcodable α] [Primcodable β]
  [Primcodable γ] [Primcodable σ]

/-- Total list folding with a computable, parameter-dependent step. -/
theorem cfoldl (f : α → List β) (g : α → σ) (h : α → σ × β → σ)
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun s b => h a (s,b)) (g a)) := by
  let step : (α × List β × σ) → σ ⊕ (α × List β × σ) := fun z =>
    match z.2.1.head? with
    | none => .inl z.2.2
    | some b => .inr (z.1,z.2.1.tail,h z.1 (z.2.2,b))
  have hsc : Computable (fun z : α × List β × σ =>
      Option.casesOn (motive := fun _ => σ ⊕ (α × List β × σ)) z.2.1.head?
        (Sum.inl z.2.2) (fun b => Sum.inr (z.1,z.2.1.tail,h z.1 (z.2.2,b)))) := by
    apply Computable.option_casesOn
      (Primrec.list_head?.to_comp.comp (Computable.fst.comp Computable.snd))
      (Computable.sumInl.comp (Computable.snd.comp Computable.snd))
    exact (Computable.sumInr.comp
      ((Computable.fst.comp Computable.fst).pair
        ((Primrec.list_tail.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
          (hh.comp (Computable.fst.comp Computable.fst)
            ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))))).to₂
  have hs : Computable step := hsc.of_eq (fun z => by
    dsimp only [step]
    cases z.2.1.head? <;> rfl)
  have hm : ∀ (a : α) (l : List β) (s : σ),
      l.foldl (fun s b => h a (s,b)) s ∈ PFun.fix (fun z => Part.some (step z)) (a,l,s) := by
    intro a l
    induction l with
    | nil => intro s; apply PFun.mem_fix_iff.mpr; left; simp [step]
    | cons b l ih =>
      intro s
      apply PFun.mem_fix_iff.mpr
      right
      exact ⟨(a,l,h a (s,b)),by simp [step],ih _⟩
  have hc : Computable (fun z : α × List β × σ =>
      z.2.1.foldl (fun s b => h z.1 (s,b)) z.2.2) :=
    hs.partrec.fix.of_eq_tot (fun z => hm z.1 z.2.1 z.2.2)
  exact hc.comp (Computable.id.pair (hf.pair hg))

theorem cfoldr (f : α → List β) (g : α → σ) (h : α → β × σ → σ)
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun b s => h a (b,s)) (g a)) := by
  have hc := cfoldl (fun a => (f a).reverse) g
    (fun a s => h a (s.2,s.1)) (Computable.list_reverse.comp hf) hg
    (hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair
      (Computable.fst.comp Computable.snd))).to₂
  exact hc.of_eq (fun a => by simp only [List.foldl_reverse])

@[fun_prop] theorem cmap (f : α → List β) (g : α × β → σ)
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => (f a).map (fun b => g (a,b))) := by
  have hc := cfoldr f (fun _ => ([] : List σ))
    (fun a z => g (a,z.1)::z.2) hf (Computable.const [])
    (Computable.list_cons.comp
      (hg.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)).to₂
  exact hc.of_eq (fun a => by induction f a <;> simp_all)

@[fun_prop] theorem cflat (f : α → List β) (g : α × β → List σ)
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => (f a).flatMap (fun b => g (a,b))) := by
  have hc := cfoldr f (fun _ => ([] : List σ))
    (fun a z => g (a,z.1)++z.2) hf (Computable.const [])
    (Computable.list_append.comp
      (hg.comp (Computable.fst.pair (Computable.fst.comp Computable.snd)))
      (Computable.snd.comp Computable.snd)).to₂
  exact hc.of_eq (fun a => by induction f a <;> simp_all)

@[fun_prop] theorem ccons (f : α → β) (g : α → List β)
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a::g a) := Computable.list_cons.comp hf hg
@[fun_prop] theorem capp (f g : α → List β) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a++g a) := Computable.list_append.comp hf hg
@[fun_prop] theorem clen (f : α → List β) (hf : Computable f) :
    Computable (fun a => (f a).length) := Computable.list_length.comp hf
@[fun_prop] theorem crange (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => List.range (f a)) := Primrec.list_range.to_comp.comp hf
@[fun_prop] theorem ctake (n : α → ℕ) (f : α → List β)
    (hn : Computable n) (hf : Computable f) :
    Computable (fun a => (f a).take (n a)) := Primrec.list_take.to_comp.comp hn hf
@[fun_prop] theorem cdrop (n : α → ℕ) (f : α → List β)
    (hn : Computable n) (hf : Computable f) :
    Computable (fun a => (f a).drop (n a)) := Primrec.list_drop.to_comp.comp hn hf
@[fun_prop] theorem cget (f : α → List β) (n : α → ℕ)
    (hf : Computable f) (hn : Computable n) :
    Computable (fun a => (f a)[n a]?) := Computable.list_getElem?.comp hf hn
@[fun_prop] theorem cgetD (f : α → Option β) (g : α → β)
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => (f a).getD (g a)) := Primrec.option_getD.to_comp.comp hf hg

@[fun_prop] theorem cadd (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a+g a) := Primrec.nat_add.to_comp.comp hf hg
@[fun_prop] theorem csub (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a-g a) := Primrec.nat_sub.to_comp.comp hf hg
@[fun_prop] theorem cmul (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a*g a) := Primrec.nat_mul.to_comp.comp hf hg
@[fun_prop] theorem cdiv (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a/g a) := Primrec.nat_div.to_comp.comp hf hg
@[fun_prop] theorem cmod (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a%g a) := Primrec.nat_mod.to_comp.comp hf hg
@[fun_prop] theorem ceq [DecidableEq β] (f g : α → β) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => decide (f a=g a)) := Primrec.eq.decide.to_comp.comp hf hg
@[fun_prop] theorem clt (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => decide (f a<g a)) := Primrec.nat_lt.decide.to_comp.comp hf hg
@[fun_prop] theorem cnot (f : α → Bool) (hf : Computable f) :
    Computable (fun a => !(f a)) := Primrec.not.to_comp.comp hf
@[fun_prop] theorem cand (f g : α → Bool) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a && g a) := Primrec.and.to_comp.comp hf hg
@[fun_prop] theorem cite (p : α → Prop) [DecidablePred p] (f g : α → β)
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) :=
  (hp.cond hf hg).of_eq (fun a => by simp only [Bool.cond_decide])
@[fun_prop] theorem cradd (f g : α → ℚ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a+g a) := UpperCoding.rat_add.comp hf hg
@[fun_prop] theorem crmul (f g : α → ℚ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a*g a) := UpperCoding.rat_mul.comp hf hg
@[fun_prop] theorem crneg (f : α → ℚ) (hf : Computable f) :
    Computable (fun a => -f a) := UpperCoding.rat_neg.comp hf
@[fun_prop] theorem crsum (f : α → List ℚ) (hf : Computable f) :
    Computable (fun a => (f a).sum) := by
  have hc := cfoldr f (fun _ => (0:ℚ)) (fun _ z => z.1+z.2) hf (Computable.const 0)
    (UpperCoding.rat_add.comp (Computable.fst.comp Computable.snd)
      (Computable.snd.comp Computable.snd)).to₂
  exact hc.of_eq (fun a => by induction f a <;> simp_all)


theorem pmem [DecidableEq β] : PrimrecRel (fun (l : List β) b => b ∈ l) :=
  Primrec.eq.exists_mem_list.of_eq (fun l b => by simp)

@[fun_prop] theorem cmem [DecidableEq β] (f : α → β) (g : α → List β)
    (hf : Computable f) (hg : Computable g) :
    Computable (fun a => decide (f a ∈ g a)) := pmem.decide.to_comp.comp hg hf

theorem dedup_primrec [DecidableEq β] : Primrec (@List.dedup β _) := by
  have hc : Primrec (fun l : List β => l.foldr
      (fun b s => if b ∈ s then s else b::s) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const [])
      (Primrec.ite (pmem.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂
  exact hc.of_eq (fun l => by induction l with
    | nil => rfl
    | cons b l ih => simp only [List.foldr_cons,ih,List.dedup_cons',List.foldr_nil])

@[fun_prop] theorem cdedup [DecidableEq β] (f : α → List β) (hf : Computable f) :
    Computable (fun a => (f a).dedup) := dedup_primrec.to_comp.comp hf


@[fun_prop] theorem clist_map (f : α → List β) (g : α → β → σ)
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).map (g a)) := cmap f (fun z => g z.1 z.2) hf hg
@[fun_prop] theorem clist_flatMap (f : α → List β) (g : α → β → List σ)
    (hf : Computable f) (hg : Computable₂ g) :
    Computable (fun a => (f a).flatMap (g a)) := cflat f (fun z => g z.1 z.2) hf hg

@[fun_prop] theorem clist_filter (f : α → List β) (p : α → β → Bool)
    (hf : Computable f) (hp : Computable₂ p) :
    Computable (fun a => (f a).filter (p a)) := by
  have hc := cfoldr f (fun _ => ([] : List β))
    (fun a z => cond (p a z.1) (z.1::z.2) z.2) hf (Computable.const [])
    ((hp.comp Computable.fst (Computable.fst.comp Computable.snd)).cond
      (Computable.list_cons.comp (Computable.fst.comp Computable.snd)
        (Computable.snd.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  exact hc.of_eq (fun a => by induction f a <;> simp_all [List.filter_cons,Bool.cond_eq_ite])


@[fun_prop] theorem cpi (f : α → β → σ)
    (hf : Computable (fun z : α × β => f z.1 z.2)) :
    Computable₂ (fun a b => f a b) := hf


@[fun_prop] theorem cconst₂ (f : β → σ) (hf : Computable f) :
    Computable₂ (fun (_ : α) b => f b) := hf.comp Computable.snd

end Sigma2.CompilerEffective
