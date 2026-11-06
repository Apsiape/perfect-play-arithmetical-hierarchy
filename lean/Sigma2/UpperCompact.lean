import Sigma2.Preliminaries

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.UpperCompact
open Filter

/-- A compact operator takes bounded weakly convergent sequences to norm limits. -/
theorem compact_weak_apply (D : Op) (hD : IsCompactOperator D) (F : ℕ → Op) (F₀ : Op)
    (hF : ∀ u v : H, Tendsto (fun n => inner ℂ u (F n v)) atTop (nhds (inner ℂ u (F₀ v))))
    (bF : ∃ C : ℝ, ∀ n, ‖F n‖ ≤ C) (v : H) :
    Tendsto (fun n => D (F n v)) atTop (nhds (D (F₀ v))) := by
  obtain ⟨C,hC⟩ := bF
  have hc := hD.isCompact_closure_image_closedBall (C*‖v‖)
  apply hc.tendsto_nhds_of_unique_mapClusterPt
  · apply Eventually.of_forall
    intro n
    apply subset_closure
    refine ⟨F n v,?_,rfl⟩
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
  · intro z _ hz
    obtain ⟨φ,hφ,hlim⟩ := hz.tendsto_subseq
    apply ext_inner_left ℂ
    intro u
    have hnorm : Tendsto (fun n => inner ℂ u (D (F (φ n) v))) atTop (nhds (inner ℂ u z)) :=
      tendsto_const_nhds.inner hlim
    have hweak : Tendsto (fun n => inner ℂ u (D (F (φ n) v))) atTop
        (nhds (inner ℂ u (D (F₀ v)))) := by
      simp only [← ContinuousLinearMap.adjoint_inner_left D]
      exact (hF (D.adjoint u) v).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique hnorm hweak

/-- Uniformly bounded operators preserve norm-null errors in weak pairings. -/
theorem pairing_error (E : ℕ → Op) (bE : ∃ C : ℝ, ∀ n, ‖E n‖ ≤ C)
    (z : ℕ → H) (hz : Tendsto z atTop (nhds 0)) (u : H) :
    Tendsto (fun n => inner ℂ u (E n (z n))) atTop (nhds 0) := by
  obtain ⟨C,hC⟩ := bE
  apply squeeze_zero_norm (fun n => ?_)
    (show Tendsto (fun n => (‖u‖*C)*‖z n‖) atTop (nhds 0) by
      simpa using tendsto_const_nhds.mul hz.norm)
  calc
    _ ≤ ‖u‖*‖E n (z n)‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖*(‖E n‖*‖z n‖) := mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ ‖u‖*(C*‖z n‖) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _)) (norm_nonneg _)
    _ = (‖u‖*C)*‖z n‖ := by ring

/-- Norm convergence of the middle factor and weak convergence of the flanks. -/
theorem sandwiches (D E F : ℕ → Op) (D₀ E₀ F₀ : Op)
    (hD : Tendsto D atTop (nhds D₀)) (hc : IsCompactOperator D₀)
    (hE : ∀ u v : H, Tendsto (fun n => inner ℂ u (E n v)) atTop (nhds (inner ℂ u (E₀ v))))
    (hF : ∀ u v : H, Tendsto (fun n => inner ℂ u (F n v)) atTop (nhds (inner ℂ u (F₀ v))))
    (bE : ∃ C : ℝ, ∀ n, ‖E n‖ ≤ C) (bF : ∃ C : ℝ, ∀ n, ‖F n‖ ≤ C) :
    ∀ u v : H, Tendsto (fun n => inner ℂ u ((E n*D n*F n) v)) atTop
      (nhds (inner ℂ u ((E₀*D₀*F₀) v))) := by
  intro u v
  have hfixed := compact_weak_apply D₀ hc F F₀ hF bF v
  have hdiff : Tendsto (fun n => (D n-D₀) (F n v)) atTop (nhds 0) := by
    obtain ⟨C,hC⟩ := bF
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => ‖D n-D₀‖*(C*‖v‖)) atTop (nhds 0) by
        simpa using (hD.sub_const D₀).norm.mul_const (C*‖v‖))
    calc
      _ ≤ ‖D n-D₀‖*‖F n v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖D n-D₀‖*(C*‖v‖) := mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))) (norm_nonneg _)
  have hfull : Tendsto (fun n => D n (F n v)) atTop (nhds (D₀ (F₀ v))) := by
    convert hdiff.add hfixed using 1 <;> simp
  have herr := pairing_error E bE (fun n => D n (F n v)-D₀ (F₀ v))
    (by simpa using hfull.sub_const (D₀ (F₀ v))) u
  have he := (hE u (D₀ (F₀ v))).add herr
  convert he using 1
  · ext n
    simp only [map_sub, inner_sub_right]
    change inner ℂ u (E n (D n (F n v))) = _
    abel
  · simp

end Sigma2.UpperCompact
