import Sigma2.UpperFiniteBorn
import Sigma2.UpperWeakLimits

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open Filter
namespace Sigma2.UpperEntropyLoss

local instance : SMul ℝ BipOp := (Module.restrictScalars ℝ ℂ BipOp).toSMul
local instance : Module ℝ BipOp := Module.restrictScalars ℝ ℂ _
local instance : Algebra ℝ BipOp := Algebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ BipOp := NormedSpace.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ BipOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : IsScalarTower ℝ ℂ BipOp where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A=(r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A

/-- Every joint POVM event has a positive complement. -/
theorem joint_complement {s} (M : Measurements s) (x : QA s) (y : QB s)
    (a : AA s) (b : BB s) : (1-M.left x a*M.right y b).IsPositive := by
  let A : AA s × BB s → BipOp := fun c => M.left x c.1*M.right y c.2
  have hsum : (∑ c,A c)=1 := by
    simp only [A,Fintype.sum_prod_type,← Finset.mul_sum,M.right_sum,mul_one,M.left_sum]
  have he : (∑ c,A c)-A (a,b)=∑ c ∈ Finset.univ.erase (a,b),A c :=
    sub_eq_iff_eq_add.mpr (Finset.sum_erase_add _ _ (Finset.mem_univ (a,b))).symm
  change (1-A (a,b)).IsPositive
  rw [← hsum,he]
  exact ContinuousLinearMap.isPositive_sum _ (fun c _ => M.joint_positive x y c.1 c.2)

/-- For a POVM event Q, its squared action is bounded by its Born probability. -/
theorem joint_norm_sq {s} (M : Measurements s) (x : QA s) (y : QB s)
    (a : AA s) (b : BB s) (v : AB) :
    ‖(M.left x a*M.right y b) v‖^2 ≤
      (inner ℂ v ((M.left x a*M.right y b) v)).re := by
  let Q := M.left x a*M.right y b
  have hQ : Q.IsPositive := M.joint_positive x y a b
  have hdiff : (Q-Q*Q).IsPositive := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    rw [show Q-Q*Q=Q*(1-Q) by rw [mul_sub,mul_one]]
    exact Commute.mul_nonneg
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hQ)
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr (joint_complement M x y a b))
      (by
        change Q*(1-Q)=(1-Q)*Q
        rw [mul_sub,sub_mul,mul_one,one_mul])
  have hh := hdiff.re_inner_nonneg_right v
  change 0 ≤ (inner ℂ v (Q v-Q (Q v))).re at hh
  rw [inner_sub_right,Complex.sub_re] at hh
  have he : ‖Q v‖^2=(inner ℂ v (Q (Q v))).re :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (Q v)).trans
      (congrArg Complex.re (hQ.isSymmetric v (Q v)))
  change ‖Q v‖^2 ≤ (inner ℂ v (Q v)).re
  linarith only [hh,he]

/-- The actual finite or infinite sandwich coefficients obey the loss estimate. -/
theorem entry_sq_le_probability {s} (S : PureStrategy s) (x : QA s) (y : QB s)
    (a : AA s) (b : BB s) (D Ftr : Op)
    (ht : ∀ i j,entry Ftr i j=entry (S.measurements.bob y b) j i)
    (hv : ∀ i j,S.vector (i,j)=entry D i j) (i j : ℕ) :
    ‖entry (S.measurements.alice x a*D*Ftr) i j‖^2 ≤ S.probability x y a b := by
  rw [← UpperAnalytic.sandwich_coordinates S.measurements x y a b D Ftr ht S.vector hv i j]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) _ _) 2).trans
      (joint_norm_sq S.measurements x y a b S.vector)

/-- Loss tending to zero forces every losing sandwich in the common WOT limit to vanish. -/
theorem zero_of_loss (G : Game) (S : ℕ → PureStrategy G.scenario)
    (D : ℕ → Op) (Ftr : ℕ → QB G.scenario → BB G.scenario → Op)
    (ht : ∀ n y b i j,entry (Ftr n y b) i j=entry ((S n).measurements.bob y b) j i)
    (hv : ∀ n i j,(S n).vector (i,j)=entry (D n) i j)
    (hl : ∀ n,loss G (normalOfPure (S n)) ≤ 1/(n+1:ℝ))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (x : QA G.scenario) (y : QB G.scenario) (a : AA G.scenario) (b : BB G.scenario)
    (hw : 0 < G.distribution x y) (ha : G.accepts x y a b=false) (L : Op)
    (hL : UpperWeakLimits.Converges
      (fun n => (S (φ n)).measurements.alice x a*D (φ n)*Ftr (φ n) y b) L) : L=0 := by
  have hw' : (0:ℝ) < G.distribution x y := by exact_mod_cast hw
  have hden : Tendsto (fun n => (φ n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by change (φ n:ℝ) ≤ (φ n:ℝ)+1; linarith)
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hzero : Tendsto (fun n => (1/(φ n+1:ℝ))/(G.distribution x y:ℝ)) atTop (nhds 0) := by
    simpa using (hden.const_div_atTop (1:ℝ)).div_const (G.distribution x y:ℝ)
  apply UpperAnalytic.entry_ext
  intro i j
  have hb n : ‖entry ((S (φ n)).measurements.alice x a*D (φ n)*Ftr (φ n) y b) i j‖^2 ≤
      (1/(φ n+1:ℝ))/(G.distribution x y:ℝ) := by
    apply (entry_sq_le_probability (S (φ n)) x y a b _ _ (ht (φ n) y b) (hv (φ n)) i j).trans
    apply (le_div_iff₀ hw').mpr
    have hh := Preliminaries.losing_event_le_loss G (normalOfPure (S (φ n))) x y a b
    rw [ha,normalOfPure_probability] at hh
    simp only [Bool.false_eq_true,ite_false] at hh
    exact (by simpa only [mul_comm] using hh.trans (hl (φ n)))
  have hh := le_of_tendsto_of_tendsto
    ((UpperWeakLimits.entry _ _ hL i j).norm.pow 2) hzero (Eventually.of_forall hb)
  have he : entry L i j=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp
    (le_antisymm hh (sq_nonneg _)))
  exact he

end Sigma2.UpperEntropyLoss


