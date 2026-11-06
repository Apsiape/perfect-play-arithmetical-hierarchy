import Sigma2.TableauStep

noncomputable section
open scoped BigOperators
namespace Sigma2.Tree

/-- Ordered products may be evaluated on a common scalar vector without any
commutation of the factors. -/
theorem ordered_update_sum (M : Automaton) (L : Option (Symbol M) → Op)
    (S N : Symbol M → Op) (E : Bool → Op) (v : H)
    (l₀ : Option (Symbol M)) (c₀ r₀ : Symbol M) (ε₀ : Bool)
    (hL : ∀ l,L l v=if l₀=l then v else 0)
    (hS : ∀ c,S c v=if c₀=c then v else 0)
    (hN : ∀ r,N r v=if r₀=r then v else 0)
    (hE : ∀ ε,E ε v=if ε₀=ε then v else 0) (a : Symbol M) :
    (∑ l,∑ c,∑ r,∑ ε : Bool,
      if M.update l c r ε=a then L l*S c*N r*E ε else 0) v=
      if M.update l₀ c₀ r₀ ε₀=a then v else 0 := by
  have term (l : Option (Symbol M)) (c r : Symbol M) (ε : Bool) :
      (if M.update l c r ε=a then L l*S c*N r*E ε else (0 : Op)) v=
        if l₀=l then if c₀=c then if r₀=r then if ε₀=ε then
          (if M.update l₀ c₀ r₀ ε₀=a then v else 0) else 0 else 0 else 0 else 0 := by
    have prod : (L l*S c*N r*E ε) v=
        if ε₀=ε then if r₀=r then if c₀=c then if l₀=l then v else 0 else 0 else 0 else 0 := by
      simp only [mul_apply_eq_comp,hE,apply_ite,map_zero,hN,hS,hL]
      split_ifs <;> rfl
    by_cases hu : M.update l c r ε=a
    · rw [if_pos hu,prod]
      by_cases hl : l₀=l <;> by_cases hc : c₀=c <;> by_cases hn : r₀=r <;>
        by_cases he : ε₀=ε <;> simp [hl,hc,hn,he,hu]
    · rw [if_neg hu,zero_apply]
      by_cases hl : l₀=l <;> by_cases hc : c₀=c <;> by_cases hn : r₀=r <;>
        by_cases he : ε₀=ε <;> simp [hl,hc,hn,he,hu]
  simp only [ContinuousLinearMap.sum_apply,term]
  simp

end Sigma2.Tree
