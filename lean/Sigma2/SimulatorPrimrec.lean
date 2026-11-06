import Sigma2.SimulatorNumbered
import Mathlib.Tactic.FunProp

noncomputable section
namespace Sigma2.SimulatorPrimrec
attribute [fun_prop] Primrec Primrec₂ PrimrecPred PrimrecRel
attribute [fun_prop] Primrec.id Primrec.const Primrec.fst Primrec.snd Primrec.comp
  Primrec.ite Primrec.pair Primrec.option_some Primrec.option_getD Primrec.fin_val PrimrecPred.and PrimrecPred.or PrimrecPred.not
  PrimrecPred.decide Primrec.dom_finite

variable {α β : Type} [Primcodable α] [Primcodable β]
@[fun_prop] theorem plt (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred (fun a => f a<g a) := Primrec.nat_lt.comp hf hg
@[fun_prop] theorem peq (f g : α → β) (hf : Primrec f) (hg : Primrec g) :
    PrimrecPred (fun a => f a=g a) := Primrec.eq.comp hf hg
@[fun_prop] theorem padd (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a+g a) := Primrec.nat_add.comp hf hg
@[fun_prop] theorem psub (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a-g a) := Primrec.nat_sub.comp hf hg
@[fun_prop] theorem pmul (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a*g a) := Primrec.nat_mul.comp hf hg
@[fun_prop] theorem pdiv (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a/g a) := Primrec.nat_div.comp hf hg
@[fun_prop] theorem pmod (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a%g a) := Primrec.nat_mod.comp hf hg
@[fun_prop] theorem pfin {n : ℕ} (f : α → ℕ) (h : ∀ a, f a<n) (hf : Primrec f) :
    Primrec (fun a => (⟨f a,h a⟩ : Fin n)) := Primrec.fin_val_iff.mp hf

open Sigma2.SimulatorNumbered
@[fun_prop] theorem fixed_enc (A : Type) [Fintype A] [Nonempty A] [Primcodable A] :
    Primrec (Coding.fixed A).enc := Primrec.dom_finite _
@[fun_prop] theorem fixed_dec (A : Type) [Fintype A] [Nonempty A] [Primcodable A] :
    Primrec (Coding.fixed A).dec := by
  have hm : Primrec (fun n : ℕ =>
      (⟨n%Fintype.card A, Nat.mod_lt _ Fintype.card_pos⟩ : Fin (Fintype.card A))) :=
    Primrec.fin_val_iff.mp (Primrec.nat_mod.comp Primrec.id (Primrec.const _))
  exact (Primrec.dom_finite (Fintype.equivFin A).symm).comp hm

example : Primrec (fun v : ℕ × ℕ => if v.1<v.2 then (v.2+1)%(v.1+1) else v.1*2) := by
  fun_prop

variable {σ : Type} [Primcodable σ]
@[fun_prop] theorem pmap (f : α → Option β) (g : α × β → σ)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).map (fun b => g (a,b))) := Primrec.option_map hf hg.to₂
@[fun_prop] theorem pbind (f : α → Option β) (g : α × β → Option σ)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).bind (fun b => g (a,b))) := Primrec.option_bind hf hg.to₂
@[fun_prop] theorem pcase (o : α → Option β) (f : α → σ) (g : α × β → σ)
    (ho : Primrec o) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (Option.casesOn (o a) (f a) (fun b => g (a,b)) : σ)) :=
  Primrec.option_casesOn ho hf hg.to₂
end Sigma2.SimulatorPrimrec


