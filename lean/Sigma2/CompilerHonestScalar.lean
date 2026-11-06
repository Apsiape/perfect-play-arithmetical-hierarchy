import Sigma2.CompilerHonestState

/-! Scalar ancillary partitions lifted to the actual infinite-dimensional
register, and their common square-root coefficient operator. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal CStarAlgebra
namespace Sigma2.CompilerHonestScalar
open FiniteAncilla CompilerHonestDensity CompilerFiniteRegister
  CompilerHonestState CoefficientOperator PureSupport
variable (d : ℕ) [NeZero d]

/-- Tensor a finite scalar matrix with one actual input operator. -/
def blocks (A : Matrix (Fin d) (Fin d) ℂ) (T : Op) : Matrix (Fin d) (Fin d) Op :=
  fun i j => A i j • T

theorem blocks_mul (A B : Matrix (Fin d) (Fin d) ℂ) (T U : Op) :
    blocks d A T*blocks d B U=blocks d (A*B) (T*U) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply,blocks,smul_mul_smul_comm]
  exact Finset.sum_smul.symm

def scalarOp (A : Matrix (Fin d) (Fin d) ℂ) : Op := matrixOp d (blocks d A 1)

@[simp] theorem scalar_zero : scalarOp d 0=0 := by
  rw [scalarOp,show blocks d 0 1=0 by ext i j; simp [blocks],matrixOp_zero]

@[simp] theorem scalar_one : scalarOp d 1=1 := by
  rw [scalarOp,show blocks d 1 1=1 by ext i j; by_cases h : i=j <;> simp [blocks,Matrix.one_apply,h],matrixOp_one]

@[simp] theorem scalar_add (A B : Matrix (Fin d) (Fin d) ℂ) :
    scalarOp d (A+B)=scalarOp d A+scalarOp d B := by
  rw [scalarOp,show blocks d (A+B) 1=blocks d A 1+blocks d B 1 by ext i j; simp [blocks,add_smul],matrixOp_add]
  rfl

@[simp] theorem scalar_mul (A B : Matrix (Fin d) (Fin d) ℂ) :
    scalarOp d (A*B)=scalarOp d A*scalarOp d B := by
  rw [scalarOp,scalarOp,scalarOp,← matrixOp_mul,blocks_mul,one_mul]

@[simp] theorem scalar_star (A : Matrix (Fin d) (Fin d) ℂ) :
    scalarOp d (star A)=star (scalarOp d A) := by
  rw [scalarOp,scalarOp,← matrixOp_star]
  congr 1
  ext i j
  simp [blocks,Matrix.star_apply,star_smul]

theorem scalar_sum {ι : Type} (s : Finset ι) (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    scalarOp d (∑ i ∈ s,A i)=∑ i ∈ s,scalarOp d (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]

def scalarPartition {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : RowCompleteness.Partition (Matrix (Fin d) (Fin d) ℂ) ι) :
    RowCompleteness.Partition Op ι where
  effect a := scalarOp d (P.effect a)
  selfadjoint a := by rw [← scalar_star,P.selfadjoint]
  product a b := by
    rw [← scalar_mul,P.product]
    split_ifs <;> simp
  total := by rw [← scalar_sum,P.total,scalar_one]

theorem matrix_entry (A : Matrix (Fin d) (Fin d) Op)
    (a b : Fin d) (i j : ℕ) :
    entry (matrixOp d A) (coordinates d (a,i)) (coordinates d (b,j))=entry (A a b) i j := by
  change FiniteSum.fiber (coordinates d) (matrixOp d A (basis (coordinates d (b,j)))) a i=_
  rw [fiber_matrixOp]
  simp only [fiber_basis]
  rw [Finset.sum_eq_single b]
  · simp only [ite_true]
    rfl
  · intro k hk hkb
    simp [hkb]
  · simp

theorem transpose_matrix (A : Matrix (Fin d) (Fin d) Op) :
    transpose (matrixOp d A)=matrixOp d (fun a b => transpose (A b a)) := by
  apply op_ext
  intro i j
  obtain ⟨⟨a,k⟩,rfl⟩ := (coordinates d).surjective i
  obtain ⟨⟨b,l⟩,rfl⟩ := (coordinates d).surjective j
  rw [transpose_entry,matrix_entry,matrix_entry,transpose_entry]

@[simp] theorem transpose_scalar (A : Matrix (Fin d) (Fin d) ℂ) :
    transpose (scalarOp d A)=scalarOp d A.transpose := by
  rw [scalarOp,transpose_matrix]
  congr 1
  ext i j
  simp [blocks,transpose_smul,transpose_one]

/-- Three scalar matrices multiply around an arbitrary common input operator.
This is the bridge from the finite FMS certificate to an actual event. -/
theorem scalar_sandwich (A C B : Matrix (Fin d) (Fin d) ℂ) (T : Op) :
    scalarOp d A*matrixOp d (blocks d C T)*transpose (scalarOp d B)=
      matrixOp d (blocks d (A*C*B.transpose) T) := by
  rw [transpose_scalar,scalarOp,scalarOp,← matrixOp_mul,← matrixOp_mul,
    blocks_mul,blocks_mul,one_mul,mul_one]

local instance : SMul ℝ Op := (Module.restrictScalars ℝ ℂ Op).toSMul
local instance : Module ℝ Op := Module.restrictScalars ℝ ℂ Op
local instance : Algebra ℝ Op := Algebra.restrictScalars ℝ ℂ Op
local instance : NormedSpace ℝ Op := NormedSpace.restrictScalars ℝ ℂ Op
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ Op
local instance : IsScalarTower ℝ ℂ Op where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A=(r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A

/-- Positive weighted densities have precisely the expected block square root. -/
theorem weighted_root (w : Fin d → ℝ) (hw : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    (h : Density) :
    root (weightedDensity d w hw hs h)=
      weightedOp d (fun i => Real.sqrt (w i)) (root h) := by
  apply CFC.sqrt_unique
  · change weightedOp d _ (root h)*weightedOp d _ (root h)=weightedOp d w h.op
    rw [weightedOp,weightedOp,← matrixOp_mul]
    congr 1
    have he (u : Fin d → ℝ) (T : Op) :
        diagonalBlocks d u T=Matrix.diagonal (fun i => (u i:ℂ) • T) := by
      ext i j
      by_cases hij : i=j <;> simp [diagonalBlocks,Matrix.diagonal_apply,hij]
    rw [he,Matrix.diagonal_mul_diagonal,he]
    congr 1
    funext i
    rw [smul_mul_smul_comm,root_square]
    congr 1
    exact_mod_cast Real.mul_self_sqrt (hw i)
  · exact ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (weighted_positive d _ (fun i => Real.sqrt_nonneg _) _ (root_positive h))

#print axioms scalarPartition
#print axioms scalar_sandwich
#print axioms weighted_root
end Sigma2.CompilerHonestScalar
