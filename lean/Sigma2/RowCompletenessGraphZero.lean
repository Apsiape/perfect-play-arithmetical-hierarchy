import Sigma2.RowCompletenessPairBlocks

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns RowWalsh FiniteAncilla

private theorem parity_at_zero (n a : ℕ) : parity n a 0=false := by
  rw [parity_symm,RowParity.parity_zero]

/-- A two-coordinate row relation is an exact shift eigen-equation on its coset. -/
theorem twoPoint_shift_eigen (n j : ℕ) (hj : j<2^n) (A : Matrix (Fin (2^n)) (Fin (2^n)) Op)
    (c : ℂ) (hc : c*c=1)
    (hrow : ∀ i,A i ⟨j,hj⟩=c • A i 0) :
    A*shift n j hj*((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect 0=
      c • (A*((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect 0) := by
  rw [coset_zero_diagonal]
  apply Matrix.ext
  intro i k
  simp only [Matrix.mul_diagonal,Matrix.smul_apply]
  rw [shift,permutation_right]
  have h0 : (xorEquiv n j hj).symm 0=⟨j,hj⟩ := by
    apply Fin.ext
    simp [xorEquiv,Nat.xor_eq]
  have hJ : (xorEquiv n j hj).symm ⟨j,hj⟩=0 := by
    apply Fin.ext
    simp [xorEquiv,Nat.xor_eq]
  by_cases hk : k.val=0 ∨ k.val=j
  · simp only [hk,ite_true,mul_one]
    rcases hk with hk | hk
    · have he : k=0 := Fin.ext hk
      subst k
      rw [h0,hrow]
    · have he : k=⟨j,hj⟩ := Fin.ext hk
      subst k
      rw [hJ,hrow,smul_smul,hc,one_smul]
  · simp only [hk,ite_false,mul_zero,smul_zero]

/-- An old event eigenprojection gives the exact two column entries needed by the graph test. -/
theorem column_event_relation (n j : ℕ) (hj : j<2^n) (V : Fin (2^n) → Op)
    (hs : ∀ i,star (V i)=V i) (h0 : V 0=1) (P : Op) (neg : Bool)
    (hjP : V ⟨j,hj⟩*P=sign neg • P) (t i : Fin (2^n)) :
    (RowColumns.column n V t*constantDiagonal (d:=2^n) P) i ⟨j,hj⟩=
      (sign (parity n t.val j)*sign neg) • (RowColumns.column n V t*constantDiagonal (d:=2^n) P) i 0 := by
  simp only [constantDiagonal,Matrix.mul_diagonal,column,Fin.val_zero,parity_at_zero,
    (show sign false=(1:ℂ) from rfl),mul_one,hs,h0,star_one,one_mul]
  simp only [smul_mul_assoc,mul_assoc,hjP,mul_smul_comm,smul_smul,mul_one]
  congr 1
  ring

/-- Every forbidden active old-bit/pair-sign outcome is killed by the honest column.
Only the matching event eigenvalue is used; different old labels never commute. -/
theorem column_pair_event_zero (n j : ℕ) (hj : j<2^n) (V : Fin (2^n) → Op)
    (hs : ∀ i,star (V i)=V i) (h0 : V 0=1) (P : Op) (neg : Bool)
    (hjP : V ⟨j,hj⟩*P=sign neg • P) (t : Fin (2^n)) (b : Bool)
    (hne : Bool.xor b neg≠parity n t.val j) :
    RowColumns.column n V t*(constantDiagonal (d:=2^n) P*(pairPartition n j hj).effect (b,0))=0 := by
  let A := RowColumns.column n V t*constantDiagonal (d:=2^n) P
  let c : ℂ := sign (parity n t.val j)*sign neg
  have hc : c*c=1 := by
    calc
      c*c=(sign (parity n t.val j)*sign (parity n t.val j))*(sign neg*sign neg) := by dsimp [c]; ring
      _ = 1 := by rw [sign_sq,sign_sq,one_mul]
  have he := twoPoint_shift_eigen n j hj A c hc
    (column_event_relation n j hj V hs h0 P neg hjP t)
  let D := ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect 0
  have hform : RowColumns.column n V t*(constantDiagonal (d:=2^n) P*(pairPartition n j hj).effect (b,0))=
      (1/2:ℂ) • (A*D+sign b • (A*shift n j hj*D)) := by
    change RowColumns.column n V t*(constantDiagonal (d:=2^n) P*(((1/2:ℂ) • (1+sign b • shift n j hj))*D))=_
    change RowColumns.column n V t*(constantDiagonal (d:=2^n) P*
      ((((1/2:ℂ) • (1+sign b • shift n j hj)) : Matrix (Fin (2^n)) (Fin (2^n)) Op)*D))=_
    rw [← mul_assoc,← mul_assoc]
    change (A*((1/2:ℂ) • (1+sign b • shift n j hj)))*D=_
    rw [Matrix.mul_smul A (1/2:ℂ) (1+sign b • shift n j hj),mul_add,mul_one,
      Matrix.mul_smul A (sign b) (shift n j hj),
      Matrix.smul_mul (1/2:ℂ) (A+sign b • (A*shift n j hj)) D,add_mul,
      Matrix.smul_mul (sign b) (A*shift n j hj) D]

  rw [hform]
  change (1/2:ℂ) • (A*D+sign b • (A*shift n j hj*D))=0
  change A*shift n j hj*D=c • (A*D) at he
  rw [he,smul_smul]
  have hsign : sign b*c= -1 := by
    dsimp [c]
    cases hp : parity n t.val j <;> cases neg <;> cases b <;> simp_all [sign,Bool.xor]
  rw [hsign,show (-1:ℂ) • (A*D)= -(A*D) from neg_one_smul ℂ (A*D),add_neg_cancel,smul_zero]

/-- An old binary event has precisely the signed reflection eigenvalue used by the table. -/
theorem binary_reflection_eigen (E : Op) (hE : Projection E) (neg b : Bool) :
    (sign neg • ((2:ℂ) • E-1))*(Partition.binary E hE.1 hE.2).effect b=
      sign (Bool.xor (!b) neg) • (Partition.binary E hE.1 hE.2).effect b := by
  cases neg <;> cases b <;>
    norm_num only [sign,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,
      Partition.binary,one_smul,neg_one_smul,smul_mul_assoc,sub_mul,mul_sub,
      mul_one,one_mul,hE.2,Bool.xor,Bool.not_false,Bool.not_true,bne_self_eq_false,Bool.false_bne,Bool.true_bne]
  all_goals module

end Sigma2.RowCompleteness
