import Sigma2.UpperFiniteAmplitudes
import Sigma2.UpperTranspose

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder Matrix ENNReal
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency.types false
namespace Sigma2.UpperCompression
open UpperFiniteOperators

@[simp] theorem cut_basis (N j : ℕ) :
    cut N (basis j) = if j<N then basis j else 0 := by
  by_cases hj : j<N
  · rw [ite_eq_left hj]
    ext i
    rw [cut_apply]
    by_cases hi : i<N
    · simp only [hi,ite_true]
    · have hij : j ≠ i := by omega
      simp [hi,basis,lp.single_apply,Pi.single_apply,hij]
  · rw [ite_eq_right hj]
    ext i
    rw [cut_apply]
    by_cases hi : i<N
    · have hij : j ≠ i := by omega
      simp [hi,basis,lp.single_apply,Pi.single_apply,hij]
    · simp [hi]

theorem extend_compress (N : ℕ) (T : Op) :
    extend N (compress N T) = cut N * T * cut N := by
  apply UpperAnalytic.entry_ext
  intro i j
  change entry (extend N (compress N T)) i j = cut N (T (cut N (basis j))) i
  rw [extend_entry,cut_basis,cut_apply]
  by_cases hi : i<N <;> by_cases hj : j<N <;> simp only [hi,hj,↓reduceDIte,ite_true,ite_false,compress,map_zero,lp.coeFn_zero,Pi.zero_apply,entry]

theorem cut_norm (N : ℕ) : ‖cut N‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  apply lp.norm_mono (by norm_num : (2:ℝ≥0∞) ≠ 0)
  intro i
  rw [cut_apply]
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using norm_nonneg (v i)

def diagonalCut (N : ℕ) (e : ℕ → ℝ) : Op :=
  extend N (Matrix.diagonal (fun i : Fin N => (e i : ℂ)))

theorem diagonalCut_left (N : ℕ) (D : Op) (e : ℕ → ℝ)
    (hd : UpperAmplitudes.Diagonal D e) : diagonalCut N e = cut N * D := by
  apply UpperAnalytic.entry_ext
  intro i j
  change entry (diagonalCut N e) i j = cut N (D (basis j)) i
  rw [cut_apply]
  change entry (diagonalCut N e) i j = if i<N then entry D i j else 0
  rw [hd]
  simp only [diagonalCut,extend_entry,Matrix.diagonal_apply]
  by_cases hi : i<N <;> by_cases hj : j<N <;> by_cases hij : i=j <;>
    simp_all [Fin.ext_iff]

theorem diagonalCut_right (N : ℕ) (D : Op) (e : ℕ → ℝ)
    (hd : UpperAmplitudes.Diagonal D e) : diagonalCut N e = D * cut N := by
  apply UpperAnalytic.entry_ext
  intro i j
  rw [diagonalCut_left N D e hd]
  change cut N (D (basis j)) i = D (cut N (basis j)) i
  rw [cut_apply]
  have hl := UpperAmplitudes.diagonal_apply hd (basis j) i
  have hr := UpperAmplitudes.diagonal_apply hd (cut N (basis j)) i
  rw [hr,cut_apply,hl]
  by_cases hi : i<N <;> simp only [hi,ite_true,ite_false,mul_zero]

theorem diagonalCut_error (N : ℕ) (D : Op) (e : ℕ → ℝ)
    (hd : UpperAmplitudes.Diagonal D e) (he : ∀ i,0≤e i) (ha : Antitone e) :
    ‖D-diagonalCut N e‖ ≤ e N := by
  apply UpperAmplitudes.norm_sub_le hd (UpperFiniteAmplitudes.pad_diagonal N (fun i => e i))
    (e N) (he N)
  intro i
  by_cases hi : i<N
  · simp [UpperFiniteAmplitudes.pad,hi,he N]
  · rw [UpperFiniteAmplitudes.pad_zero N (fun i => e i) i (Nat.le_of_not_gt hi),
      sub_zero,abs_of_nonneg (he i)]
    exact ha (Nat.le_of_not_gt hi)

/-- The finite compressed sandwich is exactly the cut of the truncated full sandwich. -/
theorem sandwich_identity (N : ℕ) (E D F : Op) (e : ℕ → ℝ)
    (hd : UpperAmplitudes.Diagonal D e) :
    extend N (compress N E * Matrix.diagonal (fun i : Fin N => (e i : ℂ)) * compress N F) =
      cut N * E * diagonalCut N e * F * cut N := by
  rw [extend_mul,extend_mul,extend_compress,extend_compress]
  change (cut N * E * cut N) * diagonalCut N e * (cut N * F * cut N) = _
  have hl : cut N * diagonalCut N e = diagonalCut N e := cut_mul_extend N _
  have hr : diagonalCut N e * cut N = diagonalCut N e := extend_mul_cut N _
  simp only [mul_assoc,hl,hr]
  rw [← mul_assoc (diagonalCut N e) (cut N) (F*cut N),hr]

theorem norm_mul_left_le (A B : Op) (hA : ‖A‖≤1) : ‖A*B‖≤‖B‖ := by
  calc
    _ ≤ ‖A‖*‖B‖ := norm_mul_le _ _
    _ ≤ 1*‖B‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ = ‖B‖ := one_mul _

theorem norm_mul_right_le (A B : Op) (hB : ‖B‖≤1) : ‖A*B‖≤‖A‖ := by
  calc
    _ ≤ ‖A‖*‖B‖ := norm_mul_le _ _
    _ ≤ ‖A‖*1 := mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    _ = ‖A‖ := mul_one _

/-- A zero full sandwich gives the common finite-compression error bound. -/
theorem sandwich_error (N : ℕ) (E D F : Op) (e : ℕ → ℝ)
    (hd : UpperAmplitudes.Diagonal D e) (he : ∀ i,0≤e i) (ha : Antitone e)
    (hE : ‖E‖≤1) (hF : ‖F‖≤1) (hz : E*D*F=0) :
    ‖extend N (compress N E * Matrix.diagonal (fun i : Fin N => (e i : ℂ)) * compress N F)‖
      ≤ e N := by
  rw [sandwich_identity N E D F e hd]
  have hz' : cut N*E*D*F*cut N=0 := by
    simpa only [mul_assoc,mul_zero,zero_mul] using congrArg (fun T : Op => cut N*T*cut N) hz
  have herr : cut N*E*(D-diagonalCut N e)*F*cut N =
      cut N*E*D*F*cut N-cut N*E*diagonalCut N e*F*cut N := by simp only [mul_sub,sub_mul]
  have hnorm : ‖cut N*E*diagonalCut N e*F*cut N‖ =
      ‖cut N*E*(D-diagonalCut N e)*F*cut N‖ := by
    rw [herr,hz',zero_sub,norm_neg]
  rw [hnorm]
  calc
    _ ≤ ‖cut N*E*(D-diagonalCut N e)*F‖ := norm_mul_right_le _ _ (cut_norm N)
    _ ≤ ‖cut N*E*(D-diagonalCut N e)‖ := norm_mul_right_le _ _ hF
    _ ≤ ‖E*(D-diagonalCut N e)‖ := by
      rw [mul_assoc]
      exact norm_mul_left_le _ _ (cut_norm N)
    _ ≤ ‖D-diagonalCut N e‖ := norm_mul_left_le _ _ hE
    _ ≤ e N := diagonalCut_error N D e hd he ha

theorem entry_norm_le (T : Op) (i j : ℕ) : ‖entry T i j‖≤‖T‖ := by
  calc
    _ ≤ ‖T (basis j)‖ := lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞)≠0) _ _
    _ ≤ ‖T‖*‖basis j‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖T‖ := by simp [basis,lp.norm_single]

/-- The exact squared-entry tolerance used by the frozen finite stage. -/
theorem compression_entry_square (κ : ℝ) (n : ℕ) (E D F : Op) (e : ℕ → ℝ)
    (hd : UpperAmplitudes.Diagonal D e) (he : ∀ i,0≤e i) (ha : Antitone e)
    (hs : Summable (fun i => e i^2)) (hb : (∑' i,e i^2)≤κ)
    (hE : ‖E‖≤1) (hF : ‖F‖≤1) (hz : E*D*F=0) (i j : Fin (n+1)) :
    ‖(compress (n+1) E * Matrix.diagonal (fun i : Fin (n+1) => (e i : ℂ)) *
      compress (n+1) F) i j‖^2 ≤ κ/(n+2) := by
  have hn := sandwich_error (n+1) E D F e hd he ha hE hF hz
  have hi := (entry_norm_le _ i j).trans hn
  rw [extend_entry_fin] at hi
  have ht : e (n+1)≤Real.sqrt (κ/(n+2)) := by
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      UpperAnalytic.square_tail e ha he hs κ hb (n+1)
  have hκ : 0≤κ := (tsum_nonneg (fun i => sq_nonneg (e i))).trans hb
  calc
    _ ≤ e (n+1)^2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
    _ ≤ (Real.sqrt (κ/(n+2)))^2 := pow_le_pow_left₀ (he _) ht 2
    _ = κ/(n+2) := Real.sq_sqrt (by positivity)

end Sigma2.UpperCompression
