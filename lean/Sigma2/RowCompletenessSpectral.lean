import Sigma2.RowCompletenessScalar
import Sigma2.RowCompletenessMeasurements

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open RowColumns TensorLifts FiniteAncilla

/-- Projection onto a reflection sign has that exact eigenvalue. -/
theorem reflection_eigen (U : Op) (hs : star U=U) (hp : U*U=1) (b : Bool) :
    (Partition.reflection U hs hp).effect b*U=
      sign b • (Partition.reflection U hs hp).effect b := by
  change ((1/2:ℂ) • (1+sign b • U))*U=sign b • ((1/2:ℂ) • (1+sign b • U))
  cases b <;> norm_num only [sign,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,
    one_smul,neg_one_smul,smul_mul_assoc,add_mul,neg_mul,one_mul,hp]
  all_goals module

/-- An exact sign eigen-operator kills the opposite spectral outcome. -/
theorem reflection_action (A U : Op) (hs : star U=U) (hp : U*U=1)
    (s b : Bool) (he : A*U=sign s • A) :
    A*(Partition.reflection U hs hp).effect b=if s=b then A else 0 := by
  change A*((1/2:ℂ) • (1+sign b • U))=if s=b then A else 0
  rw [mul_smul_comm,mul_add,mul_one,mul_smul_comm,he,smul_smul]
  cases s <;> cases b <;> norm_num [sign]
  all_goals module

/-- Commuting reflections give a four-answer joint spectral POVM. -/
def linePartition (U V : Op) (hsU : star U=U) (hsV : star V=V)
    (hqU : U*U=1) (hqV : V*V=1) (hc : U*V=V*U) : Partition Op (Bool × Bool) :=
  (Partition.reflection U hsU hqU).joint (Partition.reflection V hsV hqV) (by
    intro b c
    change ((1/2:ℂ) • (1+sign b • U))*((1/2:ℂ) • (1+sign c • V))=
      ((1/2:ℂ) • (1+sign c • V))*((1/2:ℂ) • (1+sign b • U))
    simp only [smul_mul_smul_comm,add_mul,mul_add,one_mul,mul_one,
      smul_mul_assoc,mul_smul_comm,smul_smul,hc]
    module)

/-- Finite outcome padding always gives a complete PVM on the game alphabet. -/
def padPartition {ι : Type} [Fintype ι] [DecidableEq ι] (P : Partition Op ι)
    (N : ℕ) (num : ι → ℕ) (hn : ∀ i,num i<N) : Partition Op (Fin N) :=
  P.coarse (fun i => ⟨num i,hn i⟩)

theorem padPartition_invalid {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Partition Op ι) (N : ℕ) (num : ι → ℕ) (hn : ∀ i,num i<N)
    (valid : ℕ → Bool) (hv : ∀ i,valid (num i)=true) (a : Fin N) (ha : valid a.val=false) :
    (padPartition P N num hn).effect a=0 := by
  apply Partition.coarse_outside
  intro i hi
  have he : num i=a.val := congrArg Fin.val hi
  have hh := hv i
  rw [he,ha] at hh
  contradiction

/-- Invalid padded answers also vanish when impossible raw outcomes have zero effects. -/
theorem padPartition_invalid_on_support {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Partition Op ι) (N : ℕ) (num : ι → ℕ) (hn : ∀ i,num i<N)
    (valid : ℕ → Bool) (hv : ∀ i,valid (num i)=false → P.effect i=0)
    (a : Fin N) (ha : valid a.val=false) : (padPartition P N num hn).effect a=0 := by
  change (∑ i,if (⟨num i,hn i⟩ : Fin N)=a then P.effect i else 0)=0
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with he
  · apply hv
    have hh : num i=a.val := congrArg Fin.val he
    rw [hh]
    exact ha
  · rfl

/-- The matrix realization of a constant old diagonal is the existing amplification. -/
theorem matrixOp_constantDiagonal (d : ℕ) [NeZero d] (E : Op) :
    matrixOp d (constantDiagonal E)=amplify d E := by
  ext v : 1
  apply FiniteSum.ext_fiber (coordinates d)
  intro a
  rw [fiber_matrixOp,fiber_amplify]
  rw [Finset.sum_eq_single a]
  · simp [constantDiagonal]
  · intro b hb hba; simp [constantDiagonal,Matrix.diagonal_apply,Ne.symm hba]
  · simp

theorem matrixOp_sub (d : ℕ) [NeZero d] (M N : Matrix (Fin d) (Fin d) Op) :
    matrixOp d (M-N)=matrixOp d M-matrixOp d N := by
  calc
    matrixOp d (M-N)=matrixOp d (M+(-1:ℂ) • N) := by
      rw [show (-1:ℂ) • N= -N from neg_one_smul ℂ N,sub_eq_add_neg]
    _ = matrixOp d M+(-1:ℂ) • matrixOp d N := by rw [matrixOp_add,matrixOp_smul]
    _ = matrixOp d M-matrixOp d N := by
      rw [show (-1:ℂ) • matrixOp d N= -matrixOp d N from neg_one_smul ℂ (matrixOp d N),sub_eq_add_neg]

/-- Every scalar block effect commutes with amplified old operators. -/
theorem scalarBlocks_amplify (d : ℕ) [NeZero d] (M : Matrix (Fin d) (Fin d) Op) (hM : ScalarBlocks M) (E : Op) :
    Commute (amplify d E) (matrixOp d M) := by
  rw [← matrixOp_constantDiagonal d E]
  change matrixOp d (constantDiagonal E)*matrixOp d M=matrixOp d M*matrixOp d (constantDiagonal E)
  rw [← matrixOp_mul,← matrixOp_mul,(hM E).eq]

/-- The old binary event in an old/axis question commutes with every scalar axis. -/
theorem scalarX_amplify (n : ℕ) (k : Fin n) (E : Op) : Commute (amplify (2^n) E) (scalarX n k) :=
  scalarBlocks_amplify _ _ (scalar_shift n (2^k.val) _) E

theorem scalar_phase (n j : ℕ) : ScalarBlocks (phase n j) := by
  intro E
  change constantDiagonal E*phase n j=phase n j*constantDiagonal E
  rw [constantDiagonal,phase,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul]

theorem scalarZ_amplify (n : ℕ) (k : Fin n) (E : Op) : Commute (amplify (2^n) E) (scalarZ n k) :=
  scalarBlocks_amplify _ _ (scalar_phase n (2^k.val)) E

end Sigma2.RowCompleteness
