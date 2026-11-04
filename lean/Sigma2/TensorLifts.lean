import Sigma2.NormalCoefficients
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.TensorLifts
open Coefficients

/-- Assemble square-summable columns in the completed bipartite space. -/
def ofColumns (u : ℕ → H) (hu : Summable (fun j => ‖u j‖^2)) : AB :=
  ⟨fun ij => u ij.2 ij.1, memℓp_gen (by
    have hs : Summable (fun ji : ℕ × ℕ => ‖u ji.1 ji.2‖^2) := by
      apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
      exact ⟨fun j => (norm_sq_hasSum (u j)).summable, by
        simpa only [(norm_sq_hasSum _).tsum_eq] using hu⟩
    simpa using hs.prod_symm)⟩

@[simp] theorem ofColumns_apply (u : ℕ → H) (hu) (i j : ℕ) :
    ofColumns u hu (i,j)=u j i := rfl

@[simp] theorem column_ofColumns (u : ℕ → H) (hu) (j : ℕ) :
    column (ofColumns u hu) j=u j := by ext i; rfl

theorem acted_column_summable (A : Op) (v : AB) :
    Summable (fun j => ‖A (column v j)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun j => ?_)
    ((column_mass v).1.mul_left (‖A‖^2))
  calc
    ‖A (column v j)‖^2 ≤ (‖A‖*‖column v j‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
    _ = ‖A‖^2*‖column v j‖^2 := mul_pow _ _ _

def leftVector (A : Op) (v : AB) : AB :=
  ofColumns (fun j => A (column v j)) (acted_column_summable A v)

@[simp] theorem leftVector_apply (A : Op) (v : AB) (i j : ℕ) :
    leftVector A v (i,j)=A (column v j) i := rfl

@[simp] theorem column_leftVector (A : Op) (v : AB) (j : ℕ) :
    column (leftVector A v) j=A (column v j) := by ext i; rfl

theorem leftVector_bound (A : Op) (v : AB) : ‖leftVector A v‖ ≤ ‖A‖*‖v‖ := by
  have hh : ‖leftVector A v‖^2 ≤ (‖A‖*‖v‖)^2 := by
    rw [← (column_mass (leftVector A v)).2]
    simp only [column_leftVector]
    calc
      (∑' j, ‖A (column v j)‖^2) ≤ ∑' j, ‖A‖^2*‖column v j‖^2 :=
        (acted_column_summable A v).tsum_le_tsum (fun j => by
          calc
            _ ≤ (‖A‖*‖column v j‖)^2 :=
              pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm _) 2
            _ = _ := mul_pow _ _ _)
          ((column_mass v).1.mul_left (‖A‖^2))
      _ = _ := by rw [tsum_mul_left,(column_mass v).2,mul_pow]
  nlinarith [norm_nonneg (leftVector A v),mul_nonneg (norm_nonneg A) (norm_nonneg v)]

/-- The bounded completed-space lift acting on the first tensor factor. -/
def left (A : Op) : BipOp :=
  LinearMap.mkContinuous
    { toFun := leftVector A
      map_add' := by
        intro v w
        ext ⟨i,j⟩
        have hc : column (v+w) j=column v j+column w j := by ext k; rfl
        simp only [leftVector_apply,lp.coeFn_add,Pi.add_apply,hc,map_add]
      map_smul' := by
        intro c v
        ext ⟨i,j⟩
        have hc : column (c • v) j=c • column v j := by ext k; rfl
        simp only [leftVector_apply,lp.coeFn_smul,Pi.smul_apply,hc,map_smul,
          RingHom.id_apply] }
    ‖A‖ (leftVector_bound A)

@[simp] theorem left_apply (A : Op) (v : AB) (i j : ℕ) :
    left A v (i,j)=A (column v j) i := rfl

@[simp] theorem column_left (A : Op) (v : AB) (j : ℕ) :
    column (left A v) j=A (column v j) := by ext i; rfl

/-- Coordinate exchange is an involutive unitary on the completed space. -/
def swap : AB →ₗᵢ[ℂ] AB where
  toFun v := restrict (Equiv.prodComm ℕ ℕ).toEmbedding v
  map_add' v w := by ext ⟨i,j⟩; rfl
  map_smul' c v := by ext ⟨i,j⟩; rfl
  norm_map' v := by
    have hh := (Equiv.prodComm ℕ ℕ).tsum_eq (fun ij => ‖v ij‖^2)
    have hm := (norm_sq_hasSum (restrict (Equiv.prodComm ℕ ℕ).toEmbedding v)).tsum_eq
    change (∑' ij : ℕ × ℕ, ‖v (ij.2,ij.1)‖^2)=_ at hm
    change (∑' ij : ℕ × ℕ, ‖v (ij.2,ij.1)‖^2)=∑' ij, ‖v ij‖^2 at hh
    rw [hh,(norm_sq_hasSum v).tsum_eq] at hm
    change ‖restrict (Equiv.prodComm ℕ ℕ).toEmbedding v‖=‖v‖
    nlinarith [norm_nonneg (restrict (Equiv.prodComm ℕ ℕ).toEmbedding v),norm_nonneg v]

@[simp] theorem swap_apply (v : AB) (i j : ℕ) : swap v (i,j)=v (j,i) := rfl
@[simp] theorem swap_swap (v : AB) : swap (swap v)=v := by ext ⟨i,j⟩; rfl

/-- The bounded second-factor lift, conjugated by coordinate exchange. -/
def right (B : Op) : BipOp := swap.toContinuousLinearMap.comp
  ((left B).comp swap.toContinuousLinearMap)

@[simp] theorem right_apply (B : Op) (v : AB) (i j : ℕ) :
    right B v (i,j)=B (row v i) j := by
  change B (column (swap v) i) j=_
  rfl

@[simp] theorem row_right (B : Op) (v : AB) (i : ℕ) :
    row (right B v) i=B (row v i) := by ext j; exact right_apply B v i j

theorem operator_coordinates (A : Op) (v : H) (i : ℕ) :
    A v i=∑' k,entry A i k*v k := by
  have hh := ((lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) v).mapL A).mapL
    (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 i)
  have he k : lp.single 2 k (v k)=v k • basis k := by
    simp only [basis,← lp.single_smul,smul_eq_mul,mul_one]
  change HasSum (fun k => A (lp.single 2 k (v k)) i) (A v i) at hh
  simpa only [he,map_smul,lp.coeFn_smul,Pi.smul_apply,
    smul_eq_mul,entry,mul_comm] using hh.tsum_eq.symm

theorem left_coordinates (A : Op) (v : AB) (i j : ℕ) :
    left A v (i,j)=∑' k,entry A i k*v (k,j) := operator_coordinates A (column v j) i

theorem right_coordinates (B : Op) (v : AB) (i j : ℕ) :
    right B v (i,j)=∑' k,entry B j k*v (i,k) := by
  rw [right_apply,operator_coordinates]; rfl

theorem inner_columns (v w : AB) :
    inner ℂ v w=∑' j,inner ℂ (column v j) (column w j) := by
  calc
    _ = ∑' i, ∑' j, inner ℂ (v (i,j)) (w (i,j)) :=
      (lp.summable_inner (𝕜 := ℂ) v w).tsum_prod
    _ = _ := by
      have hs : Summable (Function.uncurry (fun i j : ℕ =>
        inner ℂ (v (i,j)) (w (i,j)))) := lp.summable_inner v w
      exact hs.tsum_comm.symm

theorem inner_rows (v w : AB) :
    inner ℂ v w=∑' i,inner ℂ (row v i) (row w i) :=
  (lp.summable_inner (𝕜 := ℂ) v w).tsum_prod

theorem left_positive (A : Op) (hA : A.IsPositive) : (left A).IsPositive := by
  constructor
  · intro v w
    change inner ℂ (left A v) w=inner ℂ v (left A w)
    rw [inner_columns (left A v) w,inner_columns v (left A w)]
    simp only [column_left]
    exact tsum_congr (fun j => hA.isSymmetric _ _)
  · intro v
    change 0 ≤ (inner ℂ (left A v) v).re
    rw [inner_columns]
    simp only [column_left]
    have hs : Summable (fun j => inner ℂ (A (column v j)) (column v j)) := by
      have hh := (lp.summable_inner (𝕜 := ℂ) (left A v) v).prod_symm.prod
      simpa only [lp.inner_eq_tsum, Prod.swap, column_apply, left_apply] using hh
    change 0 ≤ Complex.reCLM (∑' j, inner ℂ (A (column v j)) (column v j))
    rw [Complex.reCLM.map_tsum hs]
    exact tsum_nonneg (fun j => hA.re_inner_nonneg_left _)

theorem right_positive (B : Op) (hB : B.IsPositive) : (right B).IsPositive := by
  constructor
  · intro v w
    change inner ℂ (right B v) w=inner ℂ v (right B w)
    rw [inner_rows (right B v) w,inner_rows v (right B w)]
    simp only [row_right]
    exact tsum_congr (fun i => hB.isSymmetric _ _)
  · intro v
    change 0 ≤ (inner ℂ (right B v) v).re
    rw [inner_rows]
    simp only [row_right]
    have hs : Summable (fun i => inner ℂ (B (row v i)) (row v i)) := by
      have hh := (lp.summable_inner (𝕜 := ℂ) (right B v) v).prod
      simpa only [lp.inner_eq_tsum, row_apply, right_apply] using hh
    change 0 ≤ Complex.reCLM (∑' i, inner ℂ (B (row v i)) (row v i))
    rw [Complex.reCLM.map_tsum hs]
    exact tsum_nonneg (fun i => hB.re_inner_nonneg_left _)

@[simp] theorem left_one : left 1=1 := by ext v ⟨i,j⟩; rfl
@[simp] theorem right_one : right 1=1 := by ext v ⟨i,j⟩; exact right_apply 1 v i j

theorem left_sum {ι : Type} (t : Finset ι) (A : ι → Op) :
    left (∑ k ∈ t,A k)=∑ k ∈ t,left (A k) := by
  ext v ⟨i,j⟩
  simp only [left_apply,sum_apply,lp.coeFn_sum,Finset.sum_apply]

theorem right_sum {ι : Type} (t : Finset ι) (A : ι → Op) :
    right (∑ k ∈ t,A k)=∑ k ∈ t,right (A k) := by
  ext v ⟨i,j⟩
  simp only [right_apply,sum_apply,lp.coeFn_sum,Finset.sum_apply]


/-- Equality on elementary coordinate vectors determines a bounded operator. -/
theorem ext_basis (L R : BipOp)
    (h : ∀ p q : ℕ, L (lp.single 2 (p,q) 1)=R (lp.single 2 (p,q) 1)) : L=R := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞)≠⊤)
  intro ⟨p,q⟩
  apply ContinuousLinearMap.ext
  intro c
  change L (lp.single 2 (p,q) c)=R (lp.single 2 (p,q) c)
  have he : (lp.single 2 (p,q) c : AB)=c • (lp.single 2 (p,q) (1:ℂ) : AB) := by
    simp only [← lp.single_smul,smul_eq_mul,mul_one]
  rw [he,map_smul,map_smul,h]

@[simp] theorem column_single (p q : ℕ) (c : ℂ) (j : ℕ) :
    column (lp.single 2 (p,q) c) j=if j=q then lp.single 2 p c else 0 := by
  ext i
  by_cases hj : j=q <;> by_cases hi : i=p <;>
    simp [column_apply,lp.single_apply,Pi.single_apply,Prod.mk.injEq,hj,hi]

@[simp] theorem row_single (p q : ℕ) (c : ℂ) (i : ℕ) :
    row (lp.single 2 (p,q) c) i=if i=p then lp.single 2 q c else 0 := by
  ext j
  by_cases hi : i=p <;> by_cases hj : j=q <;>
    simp [row_apply,lp.single_apply,Pi.single_apply,Prod.mk.injEq,hj,hi]

theorem column_right_single (B : Op) (p q j : ℕ) :
    column (right B (lp.single 2 (p,q) 1)) j=entry B j q • basis p := by
  ext i
  by_cases hi : i=p
  · subst i
    simp [column_apply,right_apply,row_single,entry,basis]
  · simp [column_apply,right_apply,row_single,entry,basis,hi,lp.single_apply,
      Pi.single_apply]

theorem row_left_single (A : Op) (p q i : ℕ) :
    row (left A (lp.single 2 (p,q) 1)) i=entry A i p • basis q := by
  ext j
  by_cases hj : j=q
  · subst j
    simp [row_apply,left_apply,column_single,entry,basis]
  · simp [row_apply,left_apply,column_single,entry,basis,hj,lp.single_apply,
      Pi.single_apply]

/-- Completed left and right actions commute; no conditional double sum is used. -/
theorem commute (A B : Op) : left A*right B=right B*left A := by
  apply ext_basis
  intro p q
  ext ⟨i,j⟩
  change left A (right B (lp.single 2 (p,q) 1)) (i,j)=
    right B (left A (lp.single 2 (p,q) 1)) (i,j)
  rw [left_apply,right_apply,column_right_single,row_left_single]
  simp only [map_smul,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,entry]
  exact mul_comm _ _

local instance : SMul ℝ BipOp := (Module.restrictScalars ℝ ℂ BipOp).toSMul
local instance : Module ℝ BipOp := Module.restrictScalars ℝ ℂ _
local instance : Algebra ℝ BipOp := Algebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ BipOp := NormedSpace.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ BipOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : IsScalarTower ℝ ℂ BipOp where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A=(r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A

theorem joint_positive (A B : Op) (hA : A.IsPositive) (hB : B.IsPositive) :
    (left A*right B).IsPositive := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mp
  exact Commute.mul_nonneg
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (left_positive A hA))
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (right_positive B hB))
    (commute A B)

@[simp] theorem left_mul (A B : Op) : left (A*B)=left A*left B := by
  ext v ⟨i,j⟩
  change A (B (column v j)) i=left A (left B v) (i,j)
  rw [left_apply,column_left]

@[simp] theorem right_mul (A B : Op) : right (A*B)=right A*right B := by
  ext v ⟨i,j⟩
  change A (B (row v i)) j=right A (right B v) (i,j)
  rw [right_apply,row_right]


/-- The canonical construction satisfies the full original POVM interface. -/
def measurements (s : Scenario)
    (E : QA s → AA s → Op) (F : QB s → BB s → Op)
    (hE : ∀ x a,Positive (E x a)) (hF : ∀ y b,Positive (F y b))
    (sE : ∀ x,∑ a,E x a=1) (sF : ∀ y,∑ b,F y b=1) : Measurements s where
  alice := E
  bob := F
  alice_pos := hE
  bob_pos := hF
  alice_sum := sE
  bob_sum := sF
  left := fun x a => left (E x a)
  right := fun y b => right (F y b)
  left_coordinates := fun x a => left_coordinates (E x a)
  right_coordinates := fun y b => right_coordinates (F y b)
  left_sum x := by rw [← left_sum, sE x, left_one]
  right_sum y := by rw [← right_sum, sF y, right_one]
  commute x y a b := commute (E x a) (F y b)
  joint_positive x y a b := joint_positive (E x a) (F y b) (hE x a) (hF y b)

theorem measurements_left {s} (M : Measurements s) (x a) :
    M.left x a=left (M.alice x a) := by
  ext v ⟨i,j⟩
  rw [M.left_coordinates,left_coordinates]

theorem measurements_right {s} (M : Measurements s) (y b) :
    M.right y b=right (M.bob y b) := by
  ext v ⟨i,j⟩
  rw [M.right_coordinates,right_coordinates]

#print axioms measurements
end Sigma2.TensorLifts
