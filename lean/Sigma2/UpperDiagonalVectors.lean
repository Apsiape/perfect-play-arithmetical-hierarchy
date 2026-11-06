import Sigma2.UpperAmplitudes

/-! Vectorization and normalization of limiting diagonal amplitudes. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace Sigma2.UpperDiagonalVectors

private theorem column_norm (d : ℕ → ℝ) (j : ℕ) : ‖(d j:ℂ) • basis j‖^2 = d j^2 := by
  rw [norm_smul]
  have hb : ‖basis j‖ = 1 := by simp [basis,lp.norm_single]
  rw [hb,mul_one,Complex.norm_real,Real.norm_eq_abs,sq_abs]

private theorem columns_summable (d : ℕ → ℝ) (hs : Summable (fun i => d i^2)) :
    Summable (fun j => ‖(d j:ℂ) • basis j‖^2) := by
  simpa only [column_norm] using hs
def vector (d : ℕ → ℝ) (hs : Summable (fun i => d i^2)) : AB :=
  TensorLifts.ofColumns (fun j => (d j:ℂ) • basis j) (columns_summable d hs)

@[simp] theorem vector_apply (d : ℕ → ℝ) (hs : Summable (fun i => d i^2)) (i j : ℕ) :
    vector d hs (i,j) = if i=j then (d i:ℂ) else 0 := by
  rw [vector,TensorLifts.ofColumns_apply]
  change (d j:ℂ) * basis j i = _
  by_cases hij : i=j <;> simp [basis,lp.single_apply,hij]

theorem vector_norm_sq (d : ℕ → ℝ) (hs : Summable (fun i => d i^2)) :
    ‖vector d hs‖^2 = ∑' i,d i^2 := by
  have h := (Coefficients.column_mass (vector d hs)).2
  simpa only [vector,TensorLifts.column_ofColumns,column_norm] using h.symm

theorem vector_ne_zero (d : ℕ → ℝ) (hs : Summable (fun i => d i^2)) (h0 : d 0=1) :
    vector d hs ≠ 0 := by
  intro h
  have hc := congrArg (fun v : AB => v (0,0)) h
  simp [h0] at hc

def normalized (d : ℕ → ℝ) (hs : Summable (fun i => d i^2)) : AB :=
  (‖vector d hs‖⁻¹:ℂ) • vector d hs

theorem normalized_unit (d : ℕ → ℝ) (hs : Summable (fun i => d i^2)) (h0 : d 0=1) :
    ‖normalized d hs‖ = 1 := by
  have hn := norm_pos_iff.mpr (vector_ne_zero d hs h0)
  simp [normalized,norm_smul,Complex.norm_real,
    inv_mul_cancel₀ (ne_of_gt hn)]

@[simp] theorem normalized_apply (d : ℕ → ℝ) (hs : Summable (fun i => d i^2)) (i j : ℕ) :
    normalized d hs (i,j) = if i=j then (d i / ‖vector d hs‖ : ℝ) else 0 := by
  by_cases hij : i=j <;> simp [normalized,hij,div_eq_mul_inv,mul_comm]

theorem coordinate_le_largest (v : AB) (i j : ℕ) : ‖v (i,j)‖^2 ≤ largestSchmidt v := by
  have hb : BddAbove {p : ℝ | ∃ u w : H, ‖u‖=1 ∧ ‖w‖=1 ∧ p=‖productOverlap v u w‖^2} := by
    refine ⟨‖v‖^2,?_⟩
    rintro p ⟨u,w,hu,hw,rfl⟩
    exact pow_le_pow_left₀ (norm_nonneg _) (UpperAnalytic.product_overlap_bound v u w hu hw) 2
  apply le_csSup hb
  refine ⟨basis i,basis j,?_,?_,?_⟩
  · simp [basis,lp.norm_single]
  · simp [basis,lp.norm_single]
  · rw [UpperAnalytic.basis_overlap]

theorem normalized_largest (d : ℕ → ℝ) (hs : Summable (fun i => d i^2))
    (h0 : d 0=1) (κ : ℕ) (_hκ : 0 < κ) (hbudget : (∑' i,d i^2) ≤ κ) :
    1/(κ:ℝ) ≤ largestSchmidt (normalized d hs) := by
  have hn := norm_pos_iff.mpr (vector_ne_zero d hs h0)
  have hb : ‖vector d hs‖^2 ≤ κ := (vector_norm_sq d hs).trans_le hbudget
  have hd := one_div_le_one_div_of_le (sq_pos_of_pos hn) hb
  calc
    1/(κ:ℝ) ≤ 1/‖vector d hs‖^2 := hd
    _ = ‖normalized d hs (0,0)‖^2 := by
      simp [normalized_apply,h0,Complex.norm_real,
        one_div,inv_pow]
    _ ≤ largestSchmidt (normalized d hs) := coordinate_le_largest _ 0 0

theorem perfect_of_losing_zero (G : Game) (S : PureStrategy G.scenario)
    (hz : ∀ x y a b, 0 < G.distribution x y → G.accepts x y a b = false → S.probability x y a b = 0) :
    Perfect G (normalOfPure S) := by
  unfold Perfect loss
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  by_cases hw : 0 < G.distribution x y
  · cases ha : G.accepts x y a b with
    | true => simp
    | false => simp [normalOfPure_probability,hz x y a b hw ha]
  · have hd : G.distribution x y = 0 := le_antisymm (le_of_not_gt hw) (G.distribution_nonneg x y)
    simp [hd]

/-- The nonzero diagonal compact limit yields the required Schmidt stratum once
its limiting POVMs and zero sandwiches have been constructed. -/
theorem stratum_of_sandwiches (G : Game) (κ : ℕ) (hκ : 0 < κ)
    (M : Measurements G.scenario) (D : Op) (d : ℕ → ℝ)
    (hs : Summable (fun i => d i^2)) (h0 : d 0=1)
    (hd : UpperAmplitudes.Diagonal D d) (hb : (∑' i,d i^2) ≤ κ)
    (Ftr : QB G.scenario → BB G.scenario → Op)
    (ht : ∀ y b i j,entry (Ftr y b) i j=entry (M.bob y b) j i)
    (hz : ∀ x y a b,0 < G.distribution x y → G.accepts x y a b=false →
      M.alice x a * D * Ftr y b = 0) : Stratum G κ := by
  let S : PureStrategy G.scenario := ⟨M,normalized d hs,normalized_unit d hs h0⟩
  refine ⟨hκ,S,perfect_of_losing_zero G S ?_,normalized_largest d hs h0 κ hκ hb⟩
  intro x y a b hw ha
  have hv (i j : ℕ) : normalized d hs (i,j) = entry ((‖vector d hs‖⁻¹:ℂ) • D) i j := by
    change normalized d hs (i,j) = (‖vector d hs‖⁻¹:ℂ) * entry D i j
    rw [hd]
    by_cases hij : i=j <;> simp [normalized_apply,hij,div_eq_mul_inv,mul_comm]
  have he : M.alice x a * ((‖vector d hs‖⁻¹:ℂ) • D) * Ftr y b = 0 := by
    simp only [mul_smul_comm,smul_mul_assoc,hz x y a b hw ha]
    exact @smul_zero ℂ Op _ _ (‖vector d hs‖⁻¹:ℂ)
  exact (UpperAnalytic.zero_sandwich M x y a b ((‖vector d hs‖⁻¹:ℂ) • D) (Ftr y b)
    (ht y b) (normalized d hs) hv).mpr he

end Sigma2.UpperDiagonalVectors
