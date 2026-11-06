import Sigma2.EntropyEnumeration

set_option synthInstance.maxHeartbeats 10000
set_option maxHeartbeats 300000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.EntropySpectrum

/-- The density trace is the sum of its eigenvalues in any Hilbert eigenbasis. -/
theorem eigenbasis_probability (h : Density) (b : HilbertBasis ℕ ℂ H) (q : ℕ → ℝ)
    (he : ∀ j, h.op (b j) = (q j : ℂ) • b j) :
    Summable q ∧ (∑' j, q j) = 1 := by
  let u : ℕ → H := fun i => Coefficients.positiveRoot h.op (basis i)
  have hu : Summable (fun i => ‖u i‖^2) := by
    convert h.diagonal_summable using 1
    funext i
    simpa [u, basis, entry, lp.inner_single_left] using
      Coefficients.sqrt_column_norm_sq h.op h.positive i
  have hu1 : (∑' i, ‖u i‖^2) = 1 := by
    convert h.trace_one using 1
    apply tsum_congr
    intro i
    simpa [u, basis, entry, lp.inner_single_left] using
      Coefficients.sqrt_column_norm_sq h.op h.positive i
  let mass : ℕ → ℕ → ℝ := fun i j => ‖inner ℂ (b j) (u i)‖^2
  have hparseval (x : H) : HasSum (fun j => ‖inner ℂ (b j) x‖^2) (‖x‖^2) := by
    simpa only [b.repr_apply_apply, b.repr.norm_map] using
      Coefficients.norm_sq_hasSum (b.repr x)
  have hm : Summable (Function.uncurry mass) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun i => (hparseval (u i)).summable, ?_⟩
    simpa only [(hparseval _).tsum_eq] using hu
  have hq (j : ℕ) : (∑' i, mass i j) = q j := by
    have hs := (Coefficients.sqrt_columns h.op h.positive (b j) (b j)).mapL Complex.reCLM
    have ht (i : ℕ) :
        (inner ℂ (b j) (u i) * inner ℂ (u i) (b j)).re = mass i j := by
      change _ = ‖inner ℂ (b j) (u i)‖^2
      rw [← inner_conj_symm (u i) (b j), Complex.mul_conj, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    have hr : (inner ℂ (b j) (h.op (b j))).re = q j := by
      rw [he, inner_smul_right, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
      simp
    change HasSum (fun i => (inner ℂ (b j) (u i) * inner ℂ (u i) (b j)).re)
      (inner ℂ (b j) (h.op (b j))).re at hs
    simpa only [ht, hr] using hs.tsum_eq
  refine ⟨?_, ?_⟩
  · have hh : Summable (fun j => ∑' i, mass i j) := hm.prod_symm.prod
    simpa only [hq] using hh
  · calc
      (∑' j, q j) = ∑' j, ∑' i, mass i j := by simp only [hq]
      _ = ∑' i, ∑' j, mass i j := by
        have hc : (∑' j, ∑' i, mass i j) = ∑' i, ∑' j, mass i j := hm.tsum_comm
        exact hc
      _ = ∑' i, ‖u i‖^2 := by simp only [mass, (hparseval _).tsum_eq]
      _ = 1 := hu1

/-- A Hilbert eigenbasis gives the full operator expansion by continuity. -/
theorem eigenbasis_expansion (h : Density) (b : HilbertBasis ℕ ℂ H) (q : ℕ → ℝ)
    (he : ∀ j, h.op (b j) = (q j : ℂ) • b j) (v : H) :
    h.op v = ∑' j, ((q j : ℂ) * inner ℂ (b j) v) • b j := by
  have hh := (b.hasSum_repr v).mapL h.op
  simpa only [map_smul, he, smul_smul, b.repr_apply_apply, mul_comm] using hh.tsum_eq.symm

#print axioms eigenbasis_probability
#print axioms eigenbasis_expansion
end Sigma2.EntropySpectrum
