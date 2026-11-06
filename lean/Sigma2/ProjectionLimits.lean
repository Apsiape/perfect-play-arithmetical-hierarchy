import Sigma2.TreeFoundation

noncomputable section
open scoped InnerProductSpace
namespace Sigma2.ProjectionLimits

/-- The real quadratic form of an orthogonal projection is its squared norm. -/
theorem re_inner_projection (Q : Op) (hQ : Projection Q) (v : H) :
    (inner ℂ v (Q v)).re=‖Q v‖^2 := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hQ.1
  have hh := hs v (Q v)
  change inner ℂ (Q v) (Q v)=inner ℂ v (Q (Q v)) at hh
  have hi : Q (Q v)=Q v := congrArg (fun A : Op => A v) hQ.2
  rw [hi] at hh
  rw [← hh]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) _

/-- A decreasing sequence of supported orthogonal projections converges strongly
once its density-weighted vectors tend to zero. No inverse-density bound is used. -/
theorem strong_zero {P} (R : NormalRealization P) (Q : ℕ → Op)
    (hQ : ∀ m,Projection (Q m))
    (hs : ∀ m,R.support*Q m=Q m)
    (hdec : ∀ m n,m≤n → Q m*Q n=Q n)
    (hρ : ∀ v,Filter.Tendsto (fun m => R.density.op (Q m v)) Filter.atTop (nhds 0)) :
    ∀ v,Filter.Tendsto (fun m => Q m v) Filter.atTop (nhds 0) := by
  intro v
  have hcross (m n : ℕ) (hmn : m≤n) :
      (inner ℂ (Q m v) (Q n v)).re=‖Q n v‖^2 := by
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hQ m).1
    have hh := hsym v (Q n v)
    change inner ℂ (Q m v) (Q n v)=inner ℂ v (Q m (Q n v)) at hh
    have hi : Q m (Q n v)=Q n v := congrArg (fun A : Op => A v) (hdec m n hmn)
    rw [hi] at hh
    rw [hh,re_inner_projection _ (hQ n)]
  have hdiff (m n : ℕ) (hmn : m≤n) :
      ‖Q m v-Q n v‖^2=‖Q m v‖^2-‖Q n v‖^2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    change ‖Q m v‖^2-2*(inner ℂ (Q m v) (Q n v)).re+‖Q n v‖^2=_
    rw [hcross m n hmn]
    ring
  have hanti : Antitone (fun m => ‖Q m v‖^2) := by
    intro m n hmn
    have hh := sq_nonneg ‖Q m v-Q n v‖
    rw [hdiff m n hmn] at hh
    linarith
  have hsq : CauchySeq (fun m => ‖Q m v‖^2) := by
    apply (tendsto_atTop_ciInf hanti ?_).cauchySeq
    exact ⟨0,by rintro _ ⟨n,rfl⟩; exact sq_nonneg _⟩
  have hcauchy : CauchySeq (fun m => Q m v) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hsq (ε^2) (sq_pos_of_pos hε)
    refine ⟨N,fun m hm n hn => ?_⟩
    have hh := hN m hm n hn
    rw [Real.dist_eq] at hh
    have he : ‖Q m v-Q n v‖^2=|‖Q m v‖^2-‖Q n v‖^2| := by
      rcases le_total m n with hmn | hnm
      · rw [hdiff m n hmn,abs_of_nonneg (sub_nonneg.mpr (hanti hmn))]
      · rw [norm_sub_rev,hdiff n m hnm,abs_of_nonpos (sub_nonpos.mpr (hanti hnm))]
        ring
    rw [dist_eq_norm]
    rw [← he] at hh
    nlinarith [norm_nonneg (Q m v-Q n v)]
  obtain ⟨l,hl⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hfix : R.support l=l := by
    have hh := (R.support.continuous.tendsto l).comp hl
    change Filter.Tendsto (fun m => R.support (Q m v)) Filter.atTop (nhds (R.support l)) at hh
    have he (m : ℕ) : R.support (Q m v)=Q m v := congrArg (fun A : Op => A v) (hs m)
    simp_rw [he] at hh
    exact tendsto_nhds_unique hh hl
  have hzero : R.density.op l=0 :=
    tendsto_nhds_unique ((R.density.op.continuous.tendsto l).comp hl) (hρ v)
  have hlzero := R.faithful_on l hfix hzero
  simpa only [hlzero] using hl

#print axioms re_inner_projection
#print axioms strong_zero
end Sigma2.ProjectionLimits