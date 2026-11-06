import Sigma2.CompilerHonestDictionaryAssembly
import Sigma2.VectorCovariance
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! One canonical purification for the honest compiler. Bob uses the genuine
coordinate transpose, including on non-real input label operators. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal CStarAlgebra
namespace Sigma2.CompilerHonestState
open Coefficients TensorLifts PureSupport CoefficientOperator

@[simp] theorem transpose_twice (A : Op) : transpose (transpose A)=A := by
  apply op_ext
  intro i j
  simp only [transpose_entry]

@[simp] theorem transpose_one : transpose (1:Op)=1 := by
  apply op_ext
  intro i j
  rw [transpose_entry]
  simp [entry,basis,lp.single_apply,Pi.single_apply,eq_comm]

@[simp] theorem transpose_add (A B : Op) : transpose (A+B)=transpose A+transpose B := by
  apply op_ext
  intro i j
  change entry (transpose (A+B)) i j=entry (transpose A) i j+entry (transpose B) i j
  rw [transpose_entry,transpose_entry,transpose_entry]
  rfl

@[simp] theorem transpose_smul (c : ℂ) (A : Op) : transpose (c • A)=c • transpose A := by
  apply op_ext
  intro i j
  change entry (transpose (c • A)) i j=c*entry (transpose A) i j
  rw [transpose_entry,transpose_entry]
  rfl

@[simp] theorem transpose_zero : transpose (0:Op)=0 := by
  apply op_ext
  intro i j
  rw [transpose_entry]
  rfl

theorem transpose_mul (A B : Op) : transpose (A*B)=transpose B*transpose A := by
  ext v : 1
  change star (star (A*B) (star v))=star (star B (star (star (star A (star v)))))
  rw [star_mul,star_star]
  rfl

local instance : SMul ℝ Op := (Module.restrictScalars ℝ ℂ Op).toSMul
local instance : Module ℝ Op := Module.restrictScalars ℝ ℂ Op
local instance : Algebra ℝ Op := Algebra.restrictScalars ℝ ℂ Op
local instance : NormedSpace ℝ Op := NormedSpace.restrictScalars ℝ ℂ Op
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ Op
local instance : IsScalarTower ℝ ℂ Op where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A=(r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A

theorem transpose_positive (A : Op) (hA : Positive A) : Positive (transpose A) := by
  let B : Op := CFC.sqrt A
  have hB : Positive B := ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg A)
  have hs : B*B=A := CFC.sqrt_mul_sqrt_self A
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr hA)
  have he : transpose A=transpose B*star (transpose B) := by
    rw [← hs,transpose_mul,transpose_star,hB.isSelfAdjoint.star_eq]
  rw [he]
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp (mul_star_self_nonneg _)

theorem transpose_projection (A : Op) (hA : Projection A) : Projection (transpose A) := by
  exact ⟨by rw [transpose_star,hA.1],by rw [← transpose_mul,hA.2]⟩

def transposedDensity (h : Density) : Density where
  op := transpose h.op
  positive := transpose_positive _ h.positive
  diagonal_summable := by simpa only [transpose_entry] using h.diagonal_summable
  trace_one := by simpa only [transpose_entry] using h.trace_one

def root (h : Density) : Op := positiveRoot h.op

theorem root_positive (h : Density) : Positive (root h) :=
  ContinuousLinearMap.nonneg_iff_isPositive.mp (CFC.sqrt_nonneg h.op)

theorem root_square (h : Density) : root h*root h=h.op :=
  CFC.sqrt_mul_sqrt_self h.op (ContinuousLinearMap.nonneg_iff_isPositive.mpr h.positive)

theorem root_column_mass (h : Density) :
    HasSum (fun j => ‖root h (basis j)‖^2) 1 := by
  convert h.diagonal_summable.hasSum using 1
  · funext j
    simpa [root,basis,entry,lp.inner_single_left,RCLike.inner_apply] using
      sqrt_column_norm_sq h.op h.positive j
  · exact h.trace_one.symm

/-- The same square-root coefficient operator is used for every question. -/
def vector (h : Density) : AB :=
  ofColumns (fun j => root h (basis j)) (root_column_mass h).summable

theorem vector_unit (h : Density) : ‖vector h‖=1 := by
  have hh := (column_mass (vector h)).2
  have he (j : ℕ) : column (vector h) j=root h (basis j) := column_ofColumns _ _ j
  simp only [he,(root_column_mass h).tsum_eq] at hh
  nlinarith [norm_nonneg (vector h)]

theorem coefficient_vector (h : Density) : coefficient (vector h)=root h := by
  apply op_ext
  intro i j
  simp only [entry,coefficient_basis,vector,column_ofColumns]

theorem root_commutes (h : Density) (A : Op) (hc : Centralizes h.op A) :
    root h*A=A*root h := by
  exact (show Commute h.op A from hc).cfcₙ_nnreal NNReal.sqrt

/-- Centralizing operators synchronize with their actual transposes. -/
theorem mirror (h : Density) (A : Op) (hc : Centralizes h.op A) :
    left A (vector h)=right (transpose A) (vector h) := by
  rw [mirror_iff,coefficient_vector,transpose_twice]
  exact (root_commutes h A hc).symm

/-- A two-sided operator equation on the coefficient map is exactly an
annihilated bipartite event. This also covers the noncentral FMS effects. -/
theorem event_zero (h : Density) (A B : Op)
    (hz : A*root h*transpose B=0) :
    (left A*right B) (vector h)=0 := by
  apply coefficient_injective
  rw [show (left A*right B) (vector h)=left A (right B (vector h)) from rfl,
    coefficient_left,coefficient_right,coefficient_vector]
  have hc0 : coefficient (0:AB)=0 := by
    apply op_ext
    intro i j
    simp [entry,coefficient_basis,column_apply]
  rw [hc0,← mul_assoc,hz]

/-- The normal model retains the single canonical unit vector. -/
def strategy {s : Scenario} (h : Density) (M : Measurements s) : NormalStrategy s :=
  normalOfPure ⟨M,vector h,vector_unit h⟩

theorem marginalA {s : Scenario} (h : Density) (M : Measurements s) :
    MarginalA (strategy h M) h := by
  intro i j
  have hc := coefficient_covariance (vector h)
  rw [coefficient_vector,(root_positive h).isSelfAdjoint.star_eq,root_square] at hc
  have he : entry (covariance (column (vector h))) i j=
      ∑' b,vector h (i,b)*star (vector h (j,b)) :=
    covariance_entry _ (column_mass (vector h)).1 i j
  rw [hc,he]
  have hw (k : ℕ) : ((if k=0 then 1 else 0 : ℝ):ℂ)=if k=0 then 1 else 0 := by
    split_ifs <;> rfl
  simp [strategy,normalOfPure,hw,ite_mul]

theorem marginalB {s : Scenario} (h : Density) (M : Measurements s) :
    MarginalB (strategy h M) (transposedDensity h) := by
  intro i j
  have hs := (root_positive h).isSelfAdjoint.star_eq
  have he (a b : ℕ) : entry (root h) a b=star (entry (root h) b a) := by
    rw [← adjoint_entry,hs]
  have hc := coefficient_covariance (vector h)
  rw [coefficient_vector,hs,root_square] at hc
  change entry (transpose h.op) i j=_
  have hec : entry (covariance (column (vector h))) j i=
      ∑' a,vector h (j,a)*star (vector h (i,a)) :=
    covariance_entry _ (column_mass (vector h)).1 j i
  rw [transpose_entry,hc,hec]
  have hw (k : ℕ) : ((if k=0 then 1 else 0 : ℝ):ℂ)=if k=0 then 1 else 0 := by
    split_ifs <;> rfl
  simp only [strategy,normalOfPure,hw,ite_mul,one_mul,zero_mul,tsum_ite_eq]
  apply tsum_congr
  intro a
  change entry (root h) j a*star (entry (root h) i a)=
    entry (root h) a i*star (entry (root h) a j)
  rw [he j a,he i a,star_star]
  exact mul_comm _ _

#print axioms transpose_positive
#print axioms vector_unit
#print axioms mirror
#print axioms event_zero
#print axioms marginalA
#print axioms marginalB
end Sigma2.CompilerHonestState
