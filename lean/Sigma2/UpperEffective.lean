import Sigma2.UpperStageSyntax

/-! Primitive-recursive generation of the polynomial part of a finite stage. -/
namespace Sigma2.UpperEffective
open Sigma2.UpperRealArithmetic Sigma2.UpperStageSyntax Primrec

attribute [fun_prop] Primrec
attribute [fun_prop] Primrec.id Primrec.const Primrec.comp Primrec.pair Primrec.fst Primrec.snd
attribute [fun_prop] Primrec.encode Primrec.sumInl Primrec.sumInr
attribute [fun_prop] UpperRealArithmetic.constant_primrec UpperRealArithmetic.var_primrec

@[fun_prop] theorem pr_nat_add : Primrec (fun p : ℕ × ℕ => p.1 + p.2) := nat_add
@[fun_prop] theorem pr_nat_mul : Primrec (fun p : ℕ × ℕ => p.1 * p.2) := nat_mul
@[fun_prop] theorem pr_add : Primrec (fun p : Poly × Poly => add p.1 p.2) := add_primrec
@[fun_prop] theorem pr_sub : Primrec (fun p : Poly × Poly => sub p.1 p.2) := sub_primrec
@[fun_prop] theorem pr_mul : Primrec (fun p : Poly × Poly => mul p.1 p.2) := mul_primrec
attribute [fun_prop] UpperRealArithmetic.neg_primrec

@[fun_prop] theorem pr_cvar : Primrec cvar := by unfold cvar; fun_prop
@[fun_prop] theorem pr_dvar : Primrec dvar := by unfold dvar; fun_prop
@[fun_prop] theorem pr_yvar : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => yvar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold yvar; fun_prop
@[fun_prop] theorem pr_zvar : Primrec (fun p : ℕ × ℕ × ℕ × ℕ => zvar p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold zvar; fun_prop
@[fun_prop] theorem pr_cmul : Primrec (fun p : CPoly × CPoly => cmul p.1 p.2) := by unfold cmul; fun_prop
@[fun_prop] theorem pr_cstar : Primrec cstar := by unfold cstar; fun_prop
@[fun_prop] theorem pr_ceq : Primrec (fun p : CPoly × CPoly => ceq p.1 p.2) := by
  unfold ceq
  exact list_cons.comp ((const true).pair (sub_primrec.comp (fst.comp fst) (fst.comp snd)))
    (list_cons.comp ((const true).pair (sub_primrec.comp (snd.comp fst) (snd.comp snd))) (const []))
@[fun_prop] theorem pr_eq : Primrec (fun p : Poly × Poly => UpperStageSyntax.eq p.1 p.2) := by
  exact list_cons.comp ((const true).pair sub_primrec) (const [])
@[fun_prop] theorem pr_le : Primrec (fun p : Poly × Poly => UpperStageSyntax.le p.1 p.2) := by
  exact list_cons.comp ((const false).pair (sub_primrec.comp snd fst)) (const [])
@[fun_prop] theorem pr_normSq : Primrec normSq := by unfold normSq; fun_prop
@[fun_prop] theorem pr_append {α : Type*} [Primcodable α] :
    Primrec (fun p : List α × List α => p.1 ++ p.2) := list_append

@[fun_prop] theorem pr_bounded {α : Type*} [Primcodable α]
    (n : α → ℕ) (f : α → ℕ → Sentence) (hn : Primrec n) (hf : Primrec (fun p : α × ℕ => f p.1 p.2)) :
    Primrec (fun p => bounded (n p) (f p)) := list_flatMap (list_range.comp hn) hf
@[fun_prop] theorem pr_ctotal {α : Type*} [Primcodable α]
    (n : α → ℕ) (f : α → ℕ → CPoly) (hn : Primrec n) (hf : Primrec (fun p : α × ℕ => f p.1 p.2)) :
    Primrec (fun p => ctotal (n p) (f p)) := by
  have hsum : Primrec csum :=
    (sum_primrec.comp (list_map .id (fst.comp snd).to₂)).pair
      (sum_primrec.comp (list_map .id (snd.comp snd).to₂))
  exact hsum.comp (list_map (list_range.comp hn) hf)
@[fun_prop] theorem pr_rtotal {α : Type*} [Primcodable α]
    (n : α → ℕ) (f : α → ℕ → Poly) (hn : Primrec n) (hf : Primrec (fun p : α × ℕ => f p.1 p.2)) :
    Primrec (fun p => rtotal (n p) (f p)) := sum_primrec.comp (list_map (list_range.comp hn) hf)

@[fun_prop] theorem pr_evar : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => evar p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold evar gramN; fun_prop
@[fun_prop] theorem pr_fvar : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => fvar p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  unfold fvar gramN; fun_prop
@[fun_prop] theorem pr_sandwich : Primrec (fun p : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
    sandwich p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2.1 p.2.2.2.2.2.2) := by
  unfold sandwich; fun_prop

@[fun_prop] theorem pr_ite_le {α β : Type*} [Primcodable α] [Primcodable β]
    (i j : α → ℕ) (f g : α → β) (hi : Primrec i) (hj : Primrec j) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun p => if i p ≤ j p then f p else g p) := Primrec.ite (nat_le.comp hi hj) hf hg
@[fun_prop] theorem pr_ite_eq {α β : Type*} [Primcodable α] [Primcodable β]
    (i j : α → ℕ) (f g : α → β) (hi : Primrec i) (hj : Primrec j) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun p => if i p = j p then f p else g p) := Primrec.ite (Primrec.eq.comp hi hj) hf hg
@[fun_prop] theorem pr_ite_bool {α β : Type*} [Primcodable α] [Primcodable β]
    (c : α → Bool) (f g : α → β) (hc : Primrec c) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun p => if c p then f p else g p) := Primrec.ite (Primrec.eq.comp hc (const true)) hf hg

@[fun_prop] theorem pr_rat_natCast : Primrec (fun n : ℕ => (n:ℚ)) := by
  apply Primrec.encode_iff.mp
  refine (Primrec₂.natPair.comp (nat_mul.comp (const 2) .id) (const 1)).of_eq ?_
  intro n
  change Nat.pair (2*n) 1 = Nat.pair (Encodable.encode (n:ℚ).num) (n:ℚ).den
  simp [UpperCoding.int_encode_nat]

@[fun_prop] theorem pr_amplitudeConstraints : Primrec (fun p : ℕ × ℕ => amplitudeConstraints p.1 p.2) := by
  unfold amplitudeConstraints
  fun_prop

@[fun_prop] theorem pr_normalizationE : Primrec (fun p : ℕ × ℕ × ℕ => normalization p.1 p.2.1 p.2.2 (evar p.2.2)) := by
  unfold normalization
  fun_prop
@[fun_prop] theorem pr_normalizationF : Primrec (fun p : ℕ × ℕ × ℕ => normalization p.1 p.2.1 p.2.2 (fvar p.2.2)) := by
  unfold normalization
  fun_prop

@[fun_prop] theorem pr_losingConstraints {α : Type*} [Primcodable α]
    (q r a b m : α → ℕ) (L : α → ℕ → ℕ → ℕ → ℕ → Bool) (ε : α → ℚ)
    (hq : Primrec q) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) (hm : Primrec m)
    (hL : Primrec (fun p : α × ℕ × ℕ × ℕ × ℕ => L p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (hε : Primrec ε) :
    Primrec (fun p => losingConstraints (q p) (r p) (a p) (b p) (m p) (L p) (ε p)) := by
  unfold losingConstraints
  fun_prop

end Sigma2.UpperEffective
