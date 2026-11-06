import Sigma2.RowScalarCoordinates
import Mathlib.Data.Nat.Bitwise

noncomputable section
open scoped BigOperators
namespace Sigma2.RowParity
open RowGame

theorem parity_succ (n m v : ℕ) :
    parity (n+1) m v=Bool.xor (parity n m v) (Nat.testBit m n && Nat.testBit v n) := by
  simp [parity,List.range_succ,List.foldl_append]

theorem parity_zero (n v : ℕ) : parity n 0 v=false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [parity_succ,ih]

theorem parity_xor (n a b v : ℕ) :
    parity n (Nat.xor a b) v=Bool.xor (parity n a v) (parity n b v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [parity_succ,parity_succ,parity_succ,ih,Nat.xor_eq,Nat.testBit_xor]
    cases parity n a v <;> cases parity n b v <;>
      cases Nat.testBit a n <;> cases Nat.testBit b n <;> cases Nat.testBit v n <;> decide

theorem parity_single (n k v : ℕ) (hk : k<n) : parity n (2^k) v=Nat.testBit v k := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [parity_succ]
    by_cases hkn : k<n
    · rw [ih hkn,Nat.testBit_two_pow_of_ne (by omega)]
      simp
    · have he : k=n := by omega
      subst k
      have hz : parity n (2^n) v=false := by
        unfold parity
        have hh (l : List ℕ) (hl : ∀ i ∈ l,i<n) (b : Bool) :
            l.foldl (fun b i => Bool.xor b (Nat.testBit (2^n) i && Nat.testBit v i)) b=b := by
          induction l generalizing b with
          | nil => rfl
          | cons a l ih =>
            rw [List.foldl_cons,Nat.testBit_two_pow_of_ne (by have := hl a (by simp); omega)]
            simpa using ih (fun i hi => hl i (by simp [hi])) b
        exact hh _ (fun i hi => List.mem_range.mp hi) false
      simp [hz]

theorem bounded_ext {n a b : ℕ} (ha : a<2^n) (hb : b<2^n)
    (he : ∀ k,k<n → Nat.testBit a k=Nat.testBit b k) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k<n
  · exact he k hk
  · have hn : 2^n≤2^k := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha hn),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hn)]

theorem xor_bound {n a b : ℕ} (ha : a<2^n) (hb : b<2^n) : Nat.xor a b<2^n := by
  exact Nat.bitwise_lt_two_pow ha hb

/-- All perpendicular parities determine exactly a two-point coset. -/
theorem coset_separation {n j a b : ℕ} (hj : j<2^n) (ha : a<2^n) (hb : b<2^n)
    (hs : ∀ ell,ell<2^n → parity n ell j=false → parity n ell a=parity n ell b) :
    a=b ∨ a=Nat.xor b j := by
  by_cases hj0 : j=0
  · left
    apply bounded_ext ha hb
    intro k hk
    have hpow : 2^k<2^n := Nat.pow_lt_pow_right (by decide) hk
    simpa [parity_single n k _ hk,hj0,parity_zero] using hs (2^k) hpow (by simp [hj0,parity_single n k _ hk])
  · have hex : ∃ k,k<n ∧ Nat.testBit j k=true := by
      by_contra hh
      apply hj0
      apply bounded_ext hj (by positivity : 0<2^n)
      intro k hk
      have hn : Nat.testBit j k≠true := by intro ht; exact hh ⟨k,hk,ht⟩
      simpa using Bool.eq_false_iff.mpr hn
    obtain ⟨k,hk,hjk⟩ := hex
    have hbits (l : ℕ) (hl : l<n) :
        Bool.xor (Nat.testBit a l) (Nat.testBit b l)=
          (Nat.testBit j l && Bool.xor (Nat.testBit a k) (Nat.testBit b k)) := by
      have hp (i : ℕ) (hi : i<n) : 2^i<2^n := Nat.pow_lt_pow_right (by decide) hi
      cases hjl : Nat.testBit j l
      · have he := hs (2^l) (hp l hl) (by rw [parity_single n l j hl,hjl])
        rw [parity_single n l a hl,parity_single n l b hl] at he
        simp [hjl,he]
      · have he := hs (Nat.xor (2^l) (2^k)) (xor_bound (hp l hl) (hp k hk))
          (by rw [parity_xor,parity_single n l j hl,parity_single n k j hk,hjl,hjk]; rfl)
        rw [parity_xor,parity_xor,parity_single n l a hl,parity_single n k a hk,
          parity_single n l b hl,parity_single n k b hk] at he
        cases hla : Nat.testBit a l <;> cases hlb : Nat.testBit b l <;>
          cases hka : Nat.testBit a k <;> cases hkb : Nat.testBit b k <;> simp_all
    cases he : Bool.xor (Nat.testBit a k) (Nat.testBit b k)
    · left
      apply bounded_ext ha hb
      intro l hl
      have hh := hbits l hl
      rw [he] at hh
      clear hbits
      cases hla : Nat.testBit a l <;> cases hlb : Nat.testBit b l <;> simp_all
    · right
      apply bounded_ext ha (xor_bound hb hj)
      intro l hl
      rw [Nat.xor_eq,Nat.testBit_xor]
      have hh := hbits l hl
      rw [he] at hh
      clear hbits
      cases hla : Nat.testBit a l <;> cases hlb : Nat.testBit b l <;> cases hjl : Nat.testBit j l <;> simp_all

/-- The table's <= convention selects a unique representative, including j=0. -/
theorem canonical_unique {n j a b : ℕ} (hj : j<2^n) (ha : a<2^n) (hb : b<2^n)
    (hca : a≤Nat.xor a j) (hcb : b≤Nat.xor b j)
    (hs : ∀ ell,ell<2^n → parity n ell j=false → parity n ell a=parity n ell b) : a=b := by
  rcases coset_separation hj ha hb hs with he | he
  · exact he
  · have ht : Nat.xor a j=b := by rw [he,Nat.xor_eq,Nat.xor_eq,Nat.xor_xor_cancel_right]
    omega

#print axioms parity_succ
#print axioms parity_zero
#print axioms parity_xor
#print axioms parity_single
#print axioms bounded_ext
#print axioms xor_bound
#print axioms coset_separation
#print axioms canonical_unique
end Sigma2.RowParity


