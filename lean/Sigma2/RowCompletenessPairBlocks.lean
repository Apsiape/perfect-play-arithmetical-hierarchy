import Sigma2.RowCompletenessSpectral

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open RowGame RowColumns RowWalsh FiniteAncilla

def activeClass (c : Fin 2) : Fin 3 := ⟨c.val,by have := c.isLt; omega⟩

theorem pairClass_fiber {n : ℕ} (c : Fin 2) (a : Bool × Fin (2^n)) :
    pairClass a=activeClass c ↔ a=(decide (c.val=1),0) := by
  rcases a with ⟨b,r⟩
  constructor
  · intro he
    have hv := congrArg Fin.val he
    have hr : r.val=0 := by
      by_contra hr
      simp only [pairClass,hr,ite_false,activeClass] at hv
      change 2=c.val at hv
      have := c.isLt
      omega
    have hb : b=decide (c.val=1) := by
      simp only [pairClass,hr,ite_true,activeClass] at hv
      change (if b then 1 else 0)=c.val at hv
      cases b
      · have hc : c.val=0 := hv.symm
        rw [hc]
        rfl
      · have hc : c.val=1 := hv.symm
        rw [hc]
        rfl
    exact Prod.ext hb (Fin.ext hr)
  · intro he
    cases he
    fin_cases c <;> rfl

/-- The active slot classes are exactly the two fine zero-coset pair outcomes. -/
theorem pair_sector_active (n j : ℕ) (hj : j<2^n) (c : Fin 2) :
    ((pairPartition n j hj).coarse pairClass).effect (activeClass c)=
      (pairPartition n j hj).effect (decide (c.val=1),0) := by
  apply Partition.coarse_single
  exact pairClass_fiber c

/-- The zero coset is precisely the two-point numerical sector {0,j}. -/
theorem cosetLabel_zero (n j : ℕ) (hj : j<2^n) (i : Fin (2^n)) :
    (cosetLabel n j hj i).val=0 ↔ i.val=0 ∨ i.val=j := by
  unfold cosetLabel
  split_ifs with hi
  · change i.val=0 ↔ i.val=0 ∨ i.val=j
    constructor
    · exact Or.inl
    · rintro (he | he)
      · exact he
      · have hx : Nat.xor i.val j=0 := by simp [he,Nat.xor_eq]
        omega
  · change Nat.xor i.val j=0 ↔ i.val=0 ∨ i.val=j
    constructor
    · intro he
      right
      simpa [Nat.xor_eq] using he
    · rintro (he | he)
      · omega
      · simp [he,Nat.xor_eq]

theorem coset_zero_diagonal (n j : ℕ) (hj : j<2^n) :
    ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect 0=
      Matrix.diagonal (fun i => if i.val=0 ∨ i.val=j then (1:Op) else 0) := by
  rw [diagonal_coarse]
  congr 1
  funext i
  have he : cosetLabel n j hj i=0 ↔ i.val=0 ∨ i.val=j := by
    simpa only [Fin.ext_iff,Fin.val_zero] using cosetLabel_zero n j hj i
  simp only [he]

/-- Explicit blocks of both active pair signs, with no missing spectator cosets. -/
theorem pair_active_entry (n j : ℕ) (hj : j<2^n) (b : Bool) (i k : Fin (2^n)) :
    (pairPartition n j hj).effect (b,0) i k=
      if k.val=0 ∨ k.val=j then
        (1/2:ℂ) • ((if i=k then (1:Op) else 0)+
          sign b • (if k=(xorEquiv n j hj) i then (1:Op) else 0)) else 0 := by
  change (((1/2:ℂ) • (1+sign b • shift n j hj))*
    ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect 0) i k=_
  rw [coset_zero_diagonal,Matrix.mul_diagonal]
  by_cases hk : k.val=0 ∨ k.val=j
  · simp only [hk,ite_true,mul_one,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply,
      shift,permutationMatrix,Matrix.of_apply]
  · simp only [hk,ite_false,mul_zero]

end Sigma2.RowCompleteness
