import Sigma2.UpperFiniteOperators

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.UpperTranspose

@[simp] theorem star_basis (i : ℕ) : star (basis i) = basis i := by
  ext j
  simp [basis,lp.single_apply,Pi.single_apply]

/-- The genuine coordinate transpose, obtained by conjugating the adjoint. -/
def transpose (T : Op) : Op :=
  ((starL ℂ : H ≃L⋆[ℂ] H).toContinuousLinearMap.comp T.adjoint).comp
    (starL ℂ : H ≃L⋆[ℂ] H).toContinuousLinearMap

@[simp] theorem transpose_apply (T : Op) (v : H) :
    transpose T v = star (T.adjoint (star v)) := rfl

@[simp] theorem transpose_entry (T : Op) (i j : ℕ) :
    entry (transpose T) i j = entry T j i := by
  change star (T.adjoint (star (basis j))) i = _
  rw [star_basis,lp.star_apply]
  change star (entry T.adjoint i j) = _
  rw [← ContinuousLinearMap.star_eq_adjoint,UpperFiniteOperators.entry_star,star_star]

@[simp] theorem transpose_transpose (T : Op) : transpose (transpose T) = T := by
  apply UpperAnalytic.entry_ext
  intro i j
  simp

theorem transpose_norm_le (T : Op) : ‖transpose T‖ ≤ ‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [transpose_apply,norm_star]
  simpa using ContinuousLinearMap.le_opNorm T.adjoint (star v)

@[simp] theorem transpose_norm (T : Op) : ‖transpose T‖ = ‖T‖ := by
  exact le_antisymm (transpose_norm_le T)
    (by simpa using transpose_norm_le (transpose T))

end Sigma2.UpperTranspose
