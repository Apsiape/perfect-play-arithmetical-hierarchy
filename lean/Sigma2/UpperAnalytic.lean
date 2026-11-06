import Sigma2.Preliminaries

noncomputable section
open scoped BigOperators ComplexOrder ENNReal
namespace Sigma2.UpperAnalytic

/-- A monotone nonnegative square-summable sequence has a uniform pointwise tail bound. -/
theorem square_tail (d : ℕ → ℝ) (hd : Antitone d) (h0 : ∀ i, 0 ≤ d i)
    (hs : Summable (fun i => d i ^ 2)) (κ : ℝ)
    (hb : (∑' i, d i ^ 2) ≤ κ) (n : ℕ) :
    d n ≤ Real.sqrt (κ / (n+1)) := by
  have hsum : (n+1:ℝ) * d n ^ 2 ≤ κ := by
    calc
      _ = ∑ i ∈ Finset.range (n+1), d n ^ 2 := by simp
      _ ≤ ∑ i ∈ Finset.range (n+1), d i ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pow_le_pow_left₀ (h0 n) (hd (by simpa using Finset.mem_range.mp hi)) 2
      _ ≤ ∑' i, d i ^ 2 := hs.sum_le_tsum _ (fun i _ => sq_nonneg _)
      _ ≤ κ := hb
  have hden : (0:ℝ) < n+1 := by positivity
  have hsquare : d n ^ 2 ≤ κ/(n+1) := (le_div_iff₀ hden).mpr (by nlinarith)
  exact (Real.le_sqrt (h0 n) (le_trans (sq_nonneg _) hsquare)).mpr hsquare

/-- Coordinatewise vectorization of a bounded sandwich, with the genuine transpose. -/
theorem sandwich_coordinates {s} (M : Measurements s) (x : QA s) (y : QB s)
    (a : AA s) (b : BB s) (D Ftr : Op)
    (ht : ∀ i j, entry Ftr i j=entry (M.bob y b) j i)
    (v : AB) (hv : ∀ i j, v (i,j)=entry D i j) (i j : ℕ) :
    ((M.left x a*M.right y b) v) (i,j) = entry (M.alice x a*D*Ftr) i j := by
  have hright (i j : ℕ) : (M.right y b v) (i,j) = (D (Ftr (basis j))) i := by
    rw [M.right_coordinates, TensorLifts.operator_coordinates]
    apply tsum_congr
    intro k
    rw [hv, ← ht]
    exact mul_comm _ _
  change (M.left x a (M.right y b v)) (i,j) = _
  rw [M.left_coordinates]
  simp_rw [hright]
  exact (TensorLifts.operator_coordinates (M.alice x a) (D (Ftr (basis j))) i).symm

theorem entry_ext (L R : Op) (h : ∀ i j, entry L i j = entry R i j) : L=R := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞)≠⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro c
  have he : (lp.single 2 j c : H)=c • basis j := by
    simp only [basis, ← lp.single_smul, smul_eq_mul, mul_one]
  change L (lp.single 2 j c)=R (lp.single 2 j c)
  rw [he, map_smul, map_smul]
  congr 1
  ext i
  exact h i j

theorem zero_sandwich {s} (M : Measurements s) (x : QA s) (y : QB s)
    (a : AA s) (b : BB s) (D Ftr : Op)
    (ht : ∀ i j, entry Ftr i j=entry (M.bob y b) j i)
    (v : AB) (hv : ∀ i j, v (i,j)=entry D i j) :
    (inner ℂ v ((M.left x a*M.right y b) v)).re=0 ↔ M.alice x a*D*Ftr=0 := by
  constructor
  · intro hz
    have hzv := Preliminaries.positive_apply_eq_zero _ (M.joint_positive x y a b) v hz
    apply entry_ext
    intro i j
    rw [← sandwich_coordinates M x y a b D Ftr ht v hv, hzv]
    rfl
  · intro hz
    have hzv : (M.left x a*M.right y b) v=0 := by
      ext ⟨i,j⟩
      rw [sandwich_coordinates M x y a b D Ftr ht v hv, hz]
      rfl
    rw [hzv, inner_zero_right]
    rfl

/-- Normalized product vectors bound the coefficient supremum. -/
theorem product_overlap_bound (v : AB) (u w : H) (hu : ‖u‖=1) (hw : ‖w‖=1) :
    ‖productOverlap v u w‖ ≤ ‖v‖ := by
  have hs : Summable (fun j => ‖(w j) • u‖^2) := by
    simpa only [norm_smul, hu, mul_one] using (Coefficients.norm_sq_hasSum w).summable
  let z : AB := TensorLifts.ofColumns (fun j => (w j) • u) hs
  have hz : ‖z‖=1 := by
    have hh := (Coefficients.column_mass z).2
    simp only [z, TensorLifts.column_ofColumns, norm_smul, hu, mul_one] at hh
    rw [(Coefficients.norm_sq_hasSum w).tsum_eq, hw] at hh
    nlinarith [norm_nonneg z]
  have heq : productOverlap v u w=inner ℂ z v := by
    change (∑' ij, star (u ij.1*w ij.2)*v ij) =
      ∑' ij, inner ℂ (z ij) (v ij)
    apply tsum_congr
    intro ⟨i,j⟩
    simp only [z, TensorLifts.ofColumns_apply, lp.coeFn_smul, Pi.smul_apply,
      smul_eq_mul, RCLike.inner_apply', RCLike.star_def]
    rw [mul_comm (w j) (u i)]
  rw [heq]
  simpa only [hz, one_mul] using norm_inner_le_norm z v

theorem basis_overlap (v : AB) (i j : ℕ) : productOverlap v (basis i) (basis j)=v (i,j) := by
  unfold productOverlap
  rw [tsum_eq_single (i,j)]
  · simp [basis, lp.single_apply]
  · intro ij hij
    have hne : ij.1 ≠ i ∨ ij.2 ≠ j := by
      by_contra hn
      push_neg at hn
      exact hij (Prod.ext hn.1 hn.2)
    rcases hne with hi | hj
    · simp [basis, lp.single_apply, hi]
    · simp [basis, lp.single_apply, hj]

theorem largest_pos (v : AB) (hv : ‖v‖=1) : 0 < largestSchmidt v := by
  obtain ⟨ij,hij⟩ : ∃ ij, v ij≠0 := by
    by_contra hn
    have he : v=0 := by ext ij; exact not_not.mp (not_exists.mp hn ij)
    simpa [he] using hv
  have hb : BddAbove {p : ℝ | ∃ u w : H, ‖u‖=1 ∧ ‖w‖=1 ∧ p=‖productOverlap v u w‖^2} := by
    refine ⟨‖v‖^2,?_⟩
    rintro p ⟨u,w,hu,hw,rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (product_overlap_bound v u w hu hw) 2
  have hmem : ‖v ij‖^2 ∈ {p : ℝ | ∃ u w : H, ‖u‖=1 ∧ ‖w‖=1 ∧ p=‖productOverlap v u w‖^2} := by
    refine ⟨basis ij.1,basis ij.2,?_,?_,?_⟩
    · simp [basis,lp.norm_single]
    · simp [basis,lp.norm_single]
    · rw [basis_overlap]
  exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hij)) (le_csSup hb hmem)

end Sigma2.UpperAnalytic
