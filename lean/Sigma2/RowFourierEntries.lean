import Sigma2.RowXEntries

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates CoarseCells FiniteJoint RowColumns RowWalsh

/-- The Walsh fine operator in the already fixed matrix units. -/
def fourierUnit {d : ℕ} (n : ℕ) (t : Fin d → Fin d → Op) (a : Fin d) : Op :=
  ∑ i,∑ j,((1/(d:ℂ))*sign (parity n a.val i.val)*sign (parity n a.val j.val)) • t i j

/-- The Walsh family has exactly the original support as its total. -/
theorem fourierUnit_total {d : ℕ} (n : ℕ) (hd : d=2^n) (P : Op)
    (t : Fin d → Fin d → Op) (hu : Units P t) : ∑ a,fourierUnit n t a=P := by
  subst d
  have hn : ((2^n:ℕ):ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.two_pow_pos n))
  unfold fourierUnit
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  have he (i j : Fin (2^n)) :
      (∑ a : Fin (2^n),((1/((2^n:ℕ):ℂ))*sign (parity n a.val i.val)*sign (parity n a.val j.val)) • t i j)=
        if i=j then t i j else 0 := by
    rw [← Finset.sum_smul]
    simp only [mul_assoc,← Finset.mul_sum]
    rw [character_orthogonality]
    by_cases hij : i=j <;> simp [hij,hn]
  simp_rw [he]
  simpa using hu.total

/-- The actual bit transition acts on the Walsh operator by its table bit. -/
theorem fourierUnit_axis {d : ℕ} (n : ℕ) (hd : d=2^n) (t : Fin d → Fin d → Op)
    (A : Op) (k : Fin n)
    (ha : ∀ i j,A*t i j=t ⟨Nat.xor i.val (2^k.val),by
      exact lt_of_lt_of_eq (RowParity.xor_bound (lt_of_lt_of_eq i.isLt hd)
        (Nat.pow_lt_pow_right (by decide) k.isLt)) hd.symm⟩ j) (a : Fin d) :
    A*fourierUnit n t a=sign (Nat.testBit a.val k.val) • fourierUnit n t a := by
  subst d
  let f := xorEquiv n (2^k.val) (Nat.pow_lt_pow_right (by decide) k.isLt)
  have hf (i : Fin (2^n)) : f (f i)=i := by apply Fin.ext; simp [f,xorEquiv,Nat.xor_eq]
  have hp (i : Fin (2^n)) :
      sign (parity n a.val (f i).val)=sign (parity n a.val i.val)*sign (Nat.testBit a.val k.val) := by
    change sign (parity n a.val (Nat.xor i.val (2^k.val)))=_
    rw [parity_right_xor,parity_symm n a.val (2^k.val),RowParity.parity_single n k.val a.val k.isLt,sign_xor]
  let c := fun i j : Fin (2^n) => (1/((2^n:ℕ):ℂ))*sign (parity n a.val i.val)*sign (parity n a.val j.val)
  have hc (i j : Fin (2^n)) : c (f i) j=sign (Nat.testBit a.val k.val)*c i j := by
    dsimp [c]; rw [hp]; ring
  change A*(∑ i,∑ j,c i j • t i j)=sign (Nat.testBit a.val k.val) • (∑ i,∑ j,c i j • t i j)
  simp only [Finset.mul_sum,mul_smul_comm,ha]
  change (∑ i,∑ j,c i j • t (f i) j)=_
  rw [← Equiv.sum_comp f (fun i => ∑ j,c i j • t (f i) j)]
  simp only [hf,hc,mul_smul,Finset.smul_sum]

/-- Joint spectral selectors recover a fine operator from any complete family
    of eigenoperators; positivity of a replacement POVM is unnecessary. -/
theorem fourierUnit_joint {d : ℕ} (n : ℕ) (hd : d=2^n) (P : Op)
    (t : Fin d → Fin d → Op) (hu : Units P t)
    (A : Fin n → Op)
    (ha : ∀ k i j,A k*t i j=t ⟨Nat.xor i.val (2^k.val),by
      exact lt_of_lt_of_eq (RowParity.xor_bound (lt_of_lt_of_eq i.isLt hd)
        (Nat.pow_lt_pow_right (by decide) k.isLt)) hd.symm⟩ j) (a : Fin d) :
    intersection P (fun k => (1/2:ℂ) • (P+sign (Nat.testBit a.val k.val) • A k)) (List.finRange n)=
      fourierUnit n t a := by
  let F := fourierUnit n t
  have hP (b : Fin d) : P*F b=F b := by
    simp only [F,fourierUnit,Finset.mul_sum,mul_smul_comm,(hu.supported _ _).1]
  have he (b : Fin d) (k : Fin n) :
      ((1/2:ℂ) • (P+sign (Nat.testBit a.val k.val) • A k))*F b=
        if Nat.testBit b.val k.val=Nat.testBit a.val k.val then F b else 0 := by
    rw [smul_mul_assoc,add_mul,smul_mul_assoc,hP,fourierUnit_axis n hd t (A k) k (ha k),smul_smul]
    cases ha : Nat.testBit a.val k.val <;> cases hb : Nat.testBit b.val k.val <;>
      norm_num [sign] <;> module
  let C := intersection P (fun k => (1/2:ℂ) • (P+sign (Nat.testBit a.val k.val) • A k)) (List.finRange n)
  have hPP : P*P=P := by
    calc
      P*P = P*(∑ i,t i i) := by rw [hu.total]
      _ = ∑ i,t i i := by simp only [Finset.mul_sum,(hu.supported _ _).1]
      _ = P := hu.total
  have hC : C*P=C := intersection_supported P hPP _ _
  have hs : ∑ b,F b=P := fourierUnit_total n hd P t hu
  have hselect (b : Fin d) : C*F b=if b=a then F b else 0 := by
    dsimp only [C]
    rw [intersection_selector P (F b) _ (fun k => Nat.testBit b.val k.val)
      (fun k => Nat.testBit a.val k.val) (hP b) (he b)]
    have hh : (∀ k ∈ List.finRange n,Nat.testBit b.val k.val=Nat.testBit a.val k.val) ↔ b=a := by
      constructor
      · intro hh; apply Fin.ext
        exact RowParity.bounded_ext (by rw [← hd]; exact b.isLt) (by rw [← hd]; exact a.isLt)
          (fun k hk => hh ⟨k,hk⟩ (List.mem_finRange _))
      · intro hh; subst b; simp
    simp only [hh]
  change C=F a
  calc
    C = C*P := hC.symm
    _ = C*(∑ b,F b) := by rw [hs]
    _ = F a := by simp only [Finset.mul_sum,hselect]; simp

#print axioms fourierUnit_total
#print axioms fourierUnit_axis
#print axioms fourierUnit_joint
end Sigma2.RowScalar