import Sigma2.RowGlobalUnique
import Sigma2.RowColumns

noncomputable section
open scoped BigOperators
namespace Sigma2.RowWalsh
open Compiler RowGame RowColumns

theorem parity_symm (n a b : ℕ) : parity n a b=parity n b a := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [RowParity.parity_succ,ih,Bool.and_comm]

theorem sign_xor (a b : Bool) : sign (Bool.xor a b)=sign a*sign b := by
  cases a <;> cases b <;> norm_num [sign]

def xorEquiv (n a : ℕ) (ha : a<2^n) : Equiv.Perm (Fin (2^n)) where
  toFun t := ⟨Nat.xor t.val a,RowParity.xor_bound t.isLt ha⟩
  invFun t := ⟨Nat.xor t.val a,RowParity.xor_bound t.isLt ha⟩
  left_inv t := by apply Fin.ext; simp [Nat.xor_eq]
  right_inv t := by apply Fin.ext; simp [Nat.xor_eq]

/-- A nontrivial bounded Walsh character has zero sum, by a bit-flip bijection. -/
theorem character_sum_zero (n a : ℕ) (ha : a<2^n) (hne : a≠0) :
    ∑ t : Fin (2^n), sign (parity n t.val a)=0 := by
  have hex : ∃ k,k<n ∧ Nat.testBit a k=true := by
    by_contra hh
    apply hne
    apply RowParity.bounded_ext ha (by positivity : 0<2^n)
    intro k hk
    have hn : Nat.testBit a k≠true := by intro ht; exact hh ⟨k,hk,ht⟩
    simpa using Bool.eq_false_iff.mpr hn
  obtain ⟨k,hk,hak⟩ := hex
  have hp : 2^k<2^n := Nat.pow_lt_pow_right (by decide) hk
  have hflip (t : Fin (2^n)) :
      sign (parity n ((xorEquiv n (2^k) hp) t).val a)= -sign (parity n t.val a) := by
    change sign (parity n (Nat.xor t.val (2^k)) a)=_
    rw [RowParity.parity_xor,RowParity.parity_single n k a hk,hak,sign_xor]
    norm_num [sign]
  have he := Equiv.sum_comp (xorEquiv n (2^k) hp) (fun t : Fin (2^n) => sign (parity n t.val a))
  simp_rw [hflip] at he
  rw [Finset.sum_neg_distrib] at he
  linear_combination (-1/2:ℂ) * he

/-- Exact orthogonality for all D characters, including the constant one. -/
theorem character_orthogonality (n : ℕ) (i j : Fin (2^n)) :
    (∑ t : Fin (2^n), sign (parity n t.val i.val)*sign (parity n t.val j.val))=
      if i=j then ((2^n:ℕ):ℂ) else (0:ℂ) := by
  by_cases hij : i=j
  · subst j
    simp [sign_sq]
  · rw [ite_eq_right hij]
    have hx : Nat.xor i.val j.val≠0 := by
      intro hh
      have he : i.val=j.val := by simpa [Nat.xor_eq] using hh
      exact hij (Fin.ext he)
    have ht (t : Fin (2^n)) :
        sign (parity n t.val i.val)*sign (parity n t.val j.val)=
          sign (parity n t.val (Nat.xor i.val j.val)) := by
      rw [parity_symm n t.val (Nat.xor i.val j.val),RowParity.parity_xor,
        parity_symm n i.val t.val,parity_symm n j.val t.val,sign_xor]
    simp_rw [ht]
    exact character_sum_zero n _ (RowParity.xor_bound i.isLt j.isLt) hx

/-- The complete Walsh column partition; no commutation between V_i is used. -/
theorem column_sum (n : ℕ) (V : Fin (2^n) → Op) (hV : ∀ i,Unitary (V i)) :
    ∑ t : Fin (2^n), column n V t=1 := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.sum_apply]
  change (∑ t : Fin (2^n), column n V t i j)=(1 : Matrix _ _ Op) i j
  simp only [column,mul_assoc,← Finset.sum_smul,← Finset.mul_sum]
  rw [character_orthogonality]
  by_cases hij : i=j
  · subst j
    simp only [ite_true,Matrix.one_apply_eq,(hV i).2]
    have hn : ((2^n:ℕ):ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.two_pow_pos n))
    simp
  · simp [hij,Matrix.one_apply_ne]

/-- Distinct columns are orthogonal, even for noncommuting V_i. -/
theorem column_mul_ne (n : ℕ) (V : Fin (2^n) → Op) (hV : ∀ i,Unitary (V i))
    (t u : Fin (2^n)) (htu : t≠u) : column n V t*column n V u=0 := by
  let c : ℂ := 1/((2^n:ℕ):ℂ)
  let s := fun a b : Fin (2^n) => sign (parity n a.val b.val)
  have hunit (i j k : Fin (2^n)) :
      (V i*star (V k))*(V k*star (V j))=V i*star (V j) := by
    calc
      _ = V i*(star (V k)*V k)*star (V j) := by noncomm_ring
      _ = V i*star (V j) := by rw [(hV k).1,mul_one]
  apply Matrix.ext
  intro i j
  change (∑ k,((c*s t i*s t k) • (V i*star (V k)))*
    ((c*s u k*s u j) • (V k*star (V j))))=0
  have he (k : Fin (2^n)) :
      ((c*s t i*s t k) • (V i*star (V k)))*((c*s u k*s u j) • (V k*star (V j)))=
        ((c*c*s t i*s u j)*(s k t*s k u)) • (V i*star (V j)) := by
    rw [smul_mul_smul_comm,hunit]
    congr 1
    dsimp [s]
    rw [parity_symm n t.val k.val,parity_symm n u.val k.val]
    ring
  simp_rw [he]
  rw [← Finset.sum_smul,← Finset.mul_sum]
  change ((c*c*s t i*s u j)*(∑ k : Fin (2^n),sign (parity n k.val t.val)*sign (parity n k.val u.val))) • _=0
  rw [character_orthogonality,ite_eq_right htu,mul_zero,zero_smul]

theorem column_sum_of_dimension {d : ℕ} (n : ℕ) (hd : d=2^n)
    (V : Fin d → Op) (hV : ∀ i,Unitary (V i)) : ∑ t,column n V t=1 := by
  subst d
  exact column_sum n V hV

theorem column_mul_ne_of_dimension {d : ℕ} (n : ℕ) (hd : d=2^n)
    (V : Fin d → Op) (hV : ∀ i,Unitary (V i)) (t u : Fin d) (htu : t≠u) :
    column n V t*column n V u=0 := by
  subst d
  exact column_mul_ne n V hV t u htu

/-- All actual row columns form a complete orthogonal projection partition. -/
theorem rowColumn_partition {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) :
    (∀ t,star (rowColumn R E r t)=rowColumn R E r t ∧
      rowColumn R E r t*rowColumn R E r t=rowColumn R E r t) ∧
    (∑ t,rowColumn R E r t)=1 ∧
    ∀ t u,t≠u → rowColumn R E r t*rowColumn R E r u=0 := by
  refine ⟨fun t => rowColumn_projection R E hE r t,?_,?_⟩
  · exact column_sum_of_dimension (2*RowSlots.squares R) (RowScalar.dimension_bits R)
      (fun j => (RowSlots.slot R r j.val).eval E) (fun j => slot_unitary E hE _)
  · intro t u htu
    exact column_mul_ne_of_dimension (2*RowSlots.squares R) (RowScalar.dimension_bits R)
      (fun j => (RowSlots.slot R r j.val).eval E) (fun j => slot_unitary E hE _) t u htu

#print axioms parity_symm
#print axioms sign_xor
#print axioms character_sum_zero
#print axioms character_orthogonality
#print axioms column_sum
#print axioms column_mul_ne
#print axioms column_sum_of_dimension
#print axioms column_mul_ne_of_dimension
#print axioms rowColumn_partition
end Sigma2.RowWalsh
