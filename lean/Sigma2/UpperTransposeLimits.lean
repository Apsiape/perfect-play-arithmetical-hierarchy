import Sigma2.UpperTranspose
import Sigma2.UpperWOTCompact

noncomputable section
open scoped BigOperators InnerProductSpace
open Filter
namespace Sigma2.UpperTransposeLimits

/-- The coordinate conjugation exchanges the two slots without conjugating the pairing. -/
theorem inner_star (u v : H) : inner ℂ u (star v)=inner ℂ v (star u) := by
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro i
  simp only [lp.star_apply,RCLike.inner_apply,starRingEnd_apply]
  ring

/-- Pairing formula for the genuine transpose. -/
theorem inner_transpose (T : Op) (u v : H) :
    inner ℂ u (UpperTranspose.transpose T v)=inner ℂ (star v) (T (star u)) := by
  rw [UpperTranspose.transpose_apply,inner_star,ContinuousLinearMap.adjoint_inner_left]

theorem converges (T : ℕ → Op) (L : Op) (h : UpperWeakLimits.Converges T L) :
    UpperWeakLimits.Converges (fun n => UpperTranspose.transpose (T n)) (UpperTranspose.transpose L) := by
  intro u v
  simp only [inner_transpose]
  exact h (star v) (star u)

/-- Extension with a deterministic complementary outcome commutes with transpose. -/
theorem transpose_effect {ι : Type} [DecidableEq ι] (N : ℕ) (a₀ a : ι)
    (A : Matrix (Fin N) (Fin N) ℂ) :
    UpperTranspose.transpose (UpperFiniteOperators.effect N a₀ a A)=
      UpperFiniteOperators.effect N a₀ a A.transpose := by
  have he (i j : ℕ) :
      entry (UpperFiniteOperators.extend N A) j i =
        entry (UpperFiniteOperators.extend N A.transpose) i j := by
    by_cases hi : i<N <;> by_cases hj : j<N <;>
      simp [UpperFiniteOperators.extend_entry,hi,hj]
  have hc (i j : ℕ) :
      entry (1-UpperFiniteOperators.cut N) i j = if i = j ∧ N ≤ i then 1 else 0 := by
    change (basis j) i-UpperFiniteOperators.cut N (basis j) i = _
    rw [UpperFiniteOperators.cut_apply]
    by_cases hij : i=j
    · subst j
      by_cases hi : i<N
      · simp [hi,basis,lp.single_apply,Nat.not_le.mpr hi]
      · simp [hi,basis,lp.single_apply,Nat.le_of_not_gt hi]
    · simp [hij,Ne.symm hij,basis,lp.single_apply]
  apply UpperAnalytic.entry_ext
  intro i j
  rw [UpperTranspose.transpose_entry]
  change entry (UpperFiniteOperators.extend N A) j i +
    entry (if a=a₀ then 1-UpperFiniteOperators.cut N else 0) j i =
    entry (UpperFiniteOperators.extend N A.transpose) i j +
    entry (if a=a₀ then 1-UpperFiniteOperators.cut N else 0) i j
  rw [he]
  by_cases ha : a=a₀
  · simp only [ha,ite_true,hc]
    by_cases hij : i=j
    · subst j; rfl
    · simp [hij,Ne.symm hij]
  · simp [ha,entry]

end Sigma2.UpperTransposeLimits


