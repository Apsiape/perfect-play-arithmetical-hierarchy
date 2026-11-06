import Sigma2.UpperEntropyTruncation
import Sigma2.UpperEntropyLoss

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.UpperEntropyApproximation
open UpperEntropyTruncation UpperFiniteBorn UpperFiniteAmplitudes

local instance : SMul ℝ BipOp := (Module.restrictScalars ℝ ℂ BipOp).toSMul
local instance : Module ℝ BipOp := Module.restrictScalars ℝ ℂ _
local instance : Algebra ℝ BipOp := Algebra.restrictScalars ℝ ℂ _
local instance : NormedSpace ℝ BipOp := NormedSpace.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℝ BipOp := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : IsScalarTower ℝ ℂ BipOp where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A=(r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A

/-- A zero event on a unit vector costs at most the squared vector error. -/
theorem event_error {s} (M : Measurements s) (v w : AB)
    (x : QA s) (y : QB s) (a : AA s) (b : BB s)
    (hz : (inner ℂ v ((M.left x a*M.right y b) v)).re=0) :
    (inner ℂ w ((M.left x a*M.right y b) w)).re ≤ ‖w-v‖^2 := by
  let Q := M.left x a*M.right y b
  have hQ : Q.IsPositive := M.joint_positive x y a b
  have hzero : Q v=0 := Preliminaries.positive_apply_eq_zero Q hQ v hz
  have hnorm : ‖Q‖ ≤ 1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg Q
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr hQ)).mpr
    exact sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr
      (UpperEntropyLoss.joint_complement M x y a b))
  have hcross : inner ℂ v (Q w)=0 := by
    exact (hQ.isSymmetric v w).symm.trans (by change inner ℂ (Q v) w=0; rw [hzero,inner_zero_left])
  have he : inner ℂ (w-v) (Q (w-v))=inner ℂ w (Q w) := by
    rw [map_sub,hzero,sub_zero,inner_sub_left,hcross,sub_zero]
  rw [← he]
  apply (re_inner_le_norm (𝕜 := ℂ) (w-v) (Q (w-v))).trans
  have hh : ‖Q (w-v)‖ ≤ ‖w-v‖ := (Q.le_opNorm _).trans (by
    simpa using mul_le_mul_of_nonneg_right hnorm (norm_nonneg (w-v)))
  simpa only [pow_two] using mul_le_mul_of_nonneg_left hh (norm_nonneg (w-v))

/-- Exact overlap of the normalized finite Schmidt truncation and the original state. -/
theorem truncation_overlap (p : ℕ → ℝ) (hp : ∀ i,0 ≤ p i)
    (hs : Summable p) (ht : (∑' i,p i)=1) (ha : Antitone p)
    (m : ℕ) (hm : 0 < mass p m) :
    inner ℂ (UpperSchmidtState.vector (pad m (probabilities p m))
      (pad_nonneg _ _ (normalized_simplex p hp ha m hm).1) (pad_summable _ _))
      (UpperSchmidtState.vector p hp hs)=(Real.sqrt (mass p m):ℂ) := by
  let q := pad m (probabilities p m)
  have hq := pad_nonneg m (probabilities p m) (normalized_simplex p hp ha m hm).1
  have hv i j : UpperSchmidtState.vector q hq (pad_summable _ _) (i,j)=
      if i=j then (pad m (fun i => Real.sqrt (probabilities p m i)) i:ℂ) else 0 := by
    rw [UpperSchmidtState.vector_apply]
    by_cases hi : i<m <;> simp [q,pad,hi]
  rw [diagonal_inner m _ _ _ hv]
  have hterm (i : Fin m) :
      (Real.sqrt (probabilities p m i):ℂ)*UpperSchmidtState.vector p hp hs (i,i)=
        ((p i / Real.sqrt (mass p m):ℝ):ℂ) := by
    rw [UpperSchmidtState.vector_apply,if_pos rfl]
    change (Real.sqrt (p i/mass p m):ℂ)*(Real.sqrt (p i):ℂ)=_
    rw [Real.sqrt_div (hp i),← Complex.ofReal_mul]
    congr 1
    rw [div_mul_eq_mul_div,← pow_two,Real.sq_sqrt (hp i)]
  simp_rw [hterm]
  rw [← Complex.ofReal_sum,← Finset.sum_div]
  change ((mass p m/Real.sqrt (mass p m):ℝ):ℂ)=_
  congr 1
  exact (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hm))).mpr (by
    rw [← pow_two,Real.sq_sqrt hm.le])

/-- Normalizing the retained Schmidt mass loses at most twice the omitted mass. -/
theorem truncation_norm_sq (p : ℕ → ℝ) (hp : ∀ i,0 ≤ p i)
    (hs : Summable p) (ht : (∑' i,p i)=1) (ha : Antitone p)
    (m : ℕ) (hm : 0 < mass p m) :
    ‖UpperSchmidtState.vector (pad m (probabilities p m))
      (pad_nonneg _ _ (normalized_simplex p hp ha m hm).1) (pad_summable _ _)-
      UpperSchmidtState.vector p hp hs‖^2 ≤ 2*(∑' i,p (i+m)) := by
  have hqt : (∑' i,pad m (probabilities p m) i)=1 :=
    (pad_sum _ _).trans (normalized_simplex p hp ha m hm).2.1
  rw [norm_sub_sq (𝕜 := ℂ),
    UpperSchmidtState.vector_unit _ _ _ hqt,UpperSchmidtState.vector_unit p hp hs ht,
    truncation_overlap p hp hs ht ha m hm]
  change 1^2-2*Real.sqrt (mass p m)+1^2 ≤ _
  have hmass : mass p m ≤ 1 := mass_le_one p hp hs ht m
  have hroot : mass p m ≤ Real.sqrt (mass p m) := by
    nlinarith [Real.sq_sqrt hm.le,Real.sqrt_nonneg (mass p m),
      Real.sqrt_le_one.mpr hmass]
  have hsplit := hs.sum_add_tsum_nat_add m
  rw [ht,← Fin.sum_univ_eq_sum_range] at hsplit
  change mass p m+(∑' i,p (i+m))=1 at hsplit
  nlinarith

/-- The number of answer pairs controls the loss of a vector approximation. -/
def answerPairs (G : Game) : ℕ := (G.scenario.answersA+1)*(G.scenario.answersB+1)

theorem loss_error (G : Game) (S : PureStrategy G.scenario)
    (hS : Perfect G (normalOfPure S)) (w : AB) (hw : ‖w‖=1) :
    loss G (normalOfPure (⟨S.measurements,w,hw⟩ : PureStrategy G.scenario)) ≤
      (answerPairs G:ℝ)*‖w-S.vector‖^2 := by
  let δ := ‖w-S.vector‖^2
  have hδ : 0 ≤ δ := sq_nonneg _
  have hterm x y a b : (G.distribution x y:ℝ)*
      (if G.accepts x y a b then 0 else
        (inner ℂ w ((S.measurements.left x a*S.measurements.right y b) w)).re) ≤
      (G.distribution x y:ℝ)*δ := by
    have hweight : (0:ℝ) ≤ G.distribution x y := by exact_mod_cast G.distribution_nonneg x y
    cases ha : G.accepts x y a b with
    | true => simp only [ite_true,mul_zero]; exact mul_nonneg hweight hδ
    | false =>
      by_cases hpos : 0 < G.distribution x y
      · have hh := Preliminaries.losing_event_le_loss G (normalOfPure S) x y a b
        rw [ha,normalOfPure_probability,show loss G (normalOfPure S)=0 from hS] at hh
        simp only [Bool.false_eq_true,ite_false] at hh
        have hpos' : (0:ℝ) < G.distribution x y := by exact_mod_cast hpos
        have hz : S.probability x y a b=0 := le_antisymm
          ((mul_le_mul_iff_right₀ hpos').mp (by simpa using hh))
          (Preliminaries.pure_probability_nonnegative S x y a b)
        exact mul_le_mul_of_nonneg_left
          (event_error S.measurements S.vector w x y a b hz) hweight
      · have hz : G.distribution x y=0 := le_antisymm (not_lt.mp hpos) (G.distribution_nonneg x y)
        simp [hz]
  calc
    _ ≤ ∑ x,∑ y,∑ _a : AA G.scenario,∑ _b : BB G.scenario,(G.distribution x y:ℝ)*δ := by
      simp only [loss,normalOfPure_probability,PureStrategy.probability]
      exact Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ =>
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm x y a b
    _ = ∑ x,∑ y,(G.distribution x y:ℝ)*((answerPairs G:ℝ)*δ) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,AA,BB,Fintype.card_fin,
        answerPairs,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      ring
    _ = (answerPairs G:ℝ)*δ := by
      simp_rw [← Finset.sum_mul]
      rw [show (∑ x,∑ y,(G.distribution x y:ℝ))=1 by exact_mod_cast G.distribution_sum,one_mul]

end Sigma2.UpperEntropyApproximation
