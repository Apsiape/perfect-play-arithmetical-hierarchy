import Sigma2.TreeFoundation

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.ProjectionSeries

/-- A finite sum of mutually orthogonal projections is a projection. -/
theorem sum_projection {ι : Type} (Q : ι → Op) (hQ : ∀ i,Projection (Q i))
    (ho : ∀ i j,i≠j → Q i*Q j=0) (s : Finset ι) : Projection (∑ i ∈ s,Q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Projection,star_zero Op]
  | @insert i s hi ih =>
    have hl : Q i*(∑ j ∈ s,Q j)=0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact ho i j (fun he => hi (he.symm ▸ hj))
    have hr : (∑ j ∈ s,Q j)*Q i=0 := by
      rw [Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro j hj
      exact ho j i (fun he => hi (he ▸ hj))
    rw [Finset.sum_insert hi]
    refine ⟨?_,?_⟩
    · rw [star_add (Q i) (∑ x ∈ s,Q x),(hQ i).1,ih.1]
    · rw [add_mul,mul_add,mul_add,(hQ i).2,ih.2,hl,hr]
      abel

/-- Bessel's bound gives unconditional vector summability for every family of
mutually orthogonal projections. This does not assume completeness of the partition. -/
theorem summable {ι : Type} (Q : ι → Op) (hQ : ∀ i,Projection (Q i))
    (ho : ∀ i j,i≠j → Q i*Q j=0) (v : H) : Summable (fun i => Q i v) := by
  classical
  let E (i : ι) := LinearMap.range (Q i).toLinearMap
  let F (i : ι) : E i := ⟨Q i v,⟨v,rfl⟩⟩
  have hort : OrthogonalFamily ℂ (fun i => E i) (fun i => (E i).subtypeₗᵢ) := by
    intro i j hij x y
    obtain ⟨a,ha⟩ := x.property
    obtain ⟨b,hb⟩ := y.property
    change Q i a=(x : H) at ha
    change Q j b=(y : H) at hb
    change inner ℂ (x : H) (y : H)=0
    rw [← ha,← hb]
    have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hQ i).1
    have he : inner ℂ (Q i a) (Q j b)=inner ℂ a (Q i (Q j b)) := hs a (Q j b)
    rw [he]
    have hz : Q i (Q j b)=0 := congrArg (fun A : Op => A b) (ho i j hij)
    rw [hz,inner_zero_right]
  have hnorm (s : Finset ι) : ‖∑ i ∈ s,Q i v‖ ≤ ‖v‖ := by
    let T : Op := ∑ i ∈ s,Q i
    have ht : Projection T := sum_projection Q hQ ho s
    have he : (∑ i ∈ s,Q i v)=T v := by
      simp only [T,ContinuousLinearMap.sum_apply]
    rw [he]
    calc
      _ ≤ ‖T‖*‖v‖ := T.le_opNorm v
      _ ≤ 1*‖v‖ := mul_le_mul_of_nonneg_right (TreeFoundation.projection_norm_le T ht) (norm_nonneg v)
      _ = _ := one_mul _
  have hsq : Summable (fun i => ‖F i‖^2) := by
    apply summable_of_sum_le (fun i => sq_nonneg ‖F i‖)
    intro s
    have he := hort.norm_sum F s
    change ‖∑ i ∈ s,Q i v‖^2=∑ i ∈ s,‖F i‖^2 at he
    rw [← he]
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm s) 2
  have hh := (hort.summable_iff_norm_sq_summable F).mpr hsq
  exact hh

#print axioms sum_projection
#print axioms summable
end Sigma2.ProjectionSeries