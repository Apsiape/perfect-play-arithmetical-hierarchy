import Sigma2.RowSpectralCoordinates
import Mathlib.Logic.Equiv.Fin.Basic

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open MatrixSupportCoordinates

/-- Little-endian scalar labels: the first Pauli pair is bit 2g and
    the second is bit 2g+1, exactly as in the actual Boolean table. -/
def registerFin : (n : ℕ) → Register n ≃ Fin (4^n)
  | 0 => { toFun := fun _ => 0, invFun := fun _ => (),
           left_inv := fun _ => @Subsingleton.elim Unit _ _ _,
           right_inv := fun i => Fin.ext (by have := i.isLt; omega) }
  | n+1 =>
      ((Equiv.prodCongr ((Equiv.prodComm (Fin 2) (Fin 2)).trans finProdFinEquiv)
        (registerFin n)).trans (Equiv.prodComm (Fin 4) (Fin (4^n)))).trans
        (finProdFinEquiv.trans (finCongr (by rw [pow_succ])))

theorem registerFin_succ (n : ℕ) (i : Register (n+1)) :
    (registerFin (n+1) i).val=i.1.1.val+2*i.1.2.val+4*(registerFin n i.2).val := by
  rfl

@[simp] theorem registerFin_zero (n : ℕ) : registerFin n (zeroRegister n)=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply Fin.ext
    rw [registerFin_succ]
    simp only [zeroRegister,ih,Fin.val_zero,mul_zero,add_zero]

/-- The register bit read by a table question. -/
def registerBit : {n : ℕ} → Register n → Fin (2*n) → Bool
  | 0,_,k => Fin.elim0 k
  | n+1,i,k => if h : k.val<2 then decide ((if k.val=0 then i.1.1 else i.1.2).val=1)
      else registerBit i.2 ⟨k.val-2,by have := k.isLt; omega⟩

theorem registerFin_bit (n : ℕ) (i : Register (n+1)) :
    (registerFin (n+1) i).val=Nat.bit (decide (i.1.1.val=1))
      (Nat.bit (decide (i.1.2.val=1)) (registerFin n i.2).val) := by
  rw [registerFin_succ]
  rcases i with ⟨⟨a,b⟩,i⟩
  fin_cases a <;> fin_cases b <;> simp [Nat.bit] <;> omega

/-- Exact compatibility of every register coordinate with the actual table bit. -/
theorem registerFin_testBit (n : ℕ) (i : Register n) (k : Fin (2*n)) :
    Nat.testBit (registerFin n i).val k.val=registerBit i k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    rw [registerFin_bit]
    by_cases hk : k.val<2
    · have hh : k.val=0 ∨ k.val=1 := by omega
      rcases hh with hh | hh
      · simp [registerBit,hk,hh,Nat.testBit_bit_zero]
      · simp [registerBit,hk,hh,Nat.testBit_bit_succ,Nat.testBit_bit_zero]
    · have he : k.val=(k.val-2)+1+1 := by omega
      rw [he,Nat.testBit_bit_succ,Nat.testBit_bit_succ]
      simpa only [registerBit,dif_neg hk] using ih i.2 ⟨k.val-2,by have := k.isLt; omega⟩

/-- Blocks in the existing support coordinates, kept as ambient operators
    supported on the 00 corner. -/
def matrixBlocks {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : Op} {t : ι → ι → Op} (_hu : Units P t) (o : ι) (A : Op) : Matrix ι ι Op :=
  fun i j => t o i*A*t j o

namespace MatrixBlocks
variable {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : Op} {t : ι → ι → Op} (hu : Units P t) (o : ι)

@[simp] theorem zero : matrixBlocks hu o 0=0 := by
  apply Matrix.ext
  intro i j
  simp [matrixBlocks]

@[simp] theorem add (A B : Op) :
    matrixBlocks hu o (A+B)=matrixBlocks hu o A+matrixBlocks hu o B := by
  apply Matrix.ext
  intro i j
  simp [matrixBlocks,mul_add,add_mul]

@[simp] theorem sub (A B : Op) :
    matrixBlocks hu o (A-B)=matrixBlocks hu o A-matrixBlocks hu o B := by
  apply Matrix.ext
  intro i j
  simp [matrixBlocks,mul_sub,sub_mul]

@[simp] theorem smul (c : ℂ) (A : Op) :
    matrixBlocks hu o (c • A)=c • matrixBlocks hu o A := by
  apply Matrix.ext
  intro i j
  simp [matrixBlocks,mul_smul_comm,smul_mul_assoc]

@[simp] theorem sum {κ : Type} (s : Finset κ) (A : κ → Op) :
    matrixBlocks hu o (∑ k ∈ s,A k)=∑ k ∈ s,matrixBlocks hu o (A k) := by
  apply Matrix.ext
  intro i j
  simp [matrixBlocks,Finset.mul_sum,Finset.sum_mul,Matrix.sum_apply]

/-- Products are transported on the actual support; this also transports
    every actual forbidden zero product. -/
theorem mul (A B : Op) (hA : A*P=A) :
    matrixBlocks hu o (A*B)=matrixBlocks hu o A*matrixBlocks hu o B := by
  apply Matrix.ext
  intro i j
  change t o i*(A*B)*t j o=∑ k,(t o i*A*t k o)*(t o k*B*t j o)
  have he (k : ι) : (t o i*A*t k o)*(t o k*B*t j o)=
      t o i*A*(t k k)*B*t j o := by
    calc
      _ = t o i*A*(t k o*t o k)*B*t j o := by noncomm_ring
      _ = _ := by rw [hu.product,if_pos rfl]
  simp_rw [he]
  rw [← Finset.sum_mul,← Finset.sum_mul,← Finset.mul_sum,hu.total]
  rw [mul_assoc (t o i) A P,hA]
  noncomm_ring

/-- The matrix units have their literal scalar single-entry blocks. -/
theorem unit (k l : ι) :
    matrixBlocks hu o (t k l)=Matrix.single k l (t o o) := by
  apply Matrix.ext
  intro i j
  by_cases hik : i=k
  · subst i
    by_cases hlj : l=j
    · subst j; simp [matrixBlocks,hu.product,Matrix.single_apply]
    · have hjl : j≠l := Ne.symm hlj
      simp [matrixBlocks,hu.product,Matrix.single_apply,hlj,hjl]
  · have hki : k≠i := Ne.symm hik
    simp [matrixBlocks,hu.product,Matrix.single_apply,hik,hki]

/-- The ambient support is the diagonal corner identity. -/
theorem support : matrixBlocks hu o P=Matrix.diagonal (fun _ => t o o) := by
  apply Matrix.ext
  intro i j
  simp only [matrixBlocks,(hu.supported o i).2,hu.product]
  by_cases hij : i=j
  · subst j; simp
  · simp [hij,Matrix.diagonal_apply_ne _ hij]

/-- Supported operators are determined by these blocks. -/
theorem eq_zero (A : Op) (hL : P*A=A) (hR : A*P=A)
    (hz : matrixBlocks hu o A=0) : A=0 := by
  have he (i j : ι) : t i i*A*t j j=0 := by
    have hh := congrArg (fun M : Matrix ι ι Op => t i o*M i j*t o j) hz
    have hz' : t i o*(t o i*A*t j o)*t o j=0 := by
      simpa only [matrixBlocks,Matrix.zero_apply,mul_zero,zero_mul] using hh
    calc
      t i i*A*t j j = (t i o*t o i)*A*(t j o*t o j) := by simp only [hu.product,ite_true]
      _ = t i o*(t o i*A*t j o)*t o j := by noncomm_ring
      _ = 0 := hz'

  calc
    A = P*A*P := by rw [hL,hR]
    _ = (∑ i,t i i)*A*(∑ j,t j j) := by rw [hu.total]
    _ = 0 := by simp only [Finset.sum_mul,Finset.mul_sum,he,Finset.sum_const_zero]

end MatrixBlocks
#print axioms registerFin_zero
#print axioms registerFin_testBit
#print axioms MatrixBlocks.mul
#print axioms MatrixBlocks.unit
#print axioms MatrixBlocks.support
#print axioms MatrixBlocks.eq_zero
end Sigma2.RowScalar


