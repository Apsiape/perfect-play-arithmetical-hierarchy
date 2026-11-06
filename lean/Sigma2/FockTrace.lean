import Sigma2.TreeFoundation

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.FockTrace
open TraceProducts Coefficients TreeFoundation

/-- Transporting a normal covariance transports every square-root column. -/
theorem covariance_map (u : ℕ → H) (hu : Summable (fun i => ‖u i‖^2)) (A : Op) :
    A*covariance u*star A=covariance (fun i => A (u i)) := by
  apply ContinuousLinearMap.ext
  intro w
  apply ext_inner_left ℂ
  intro v
  have h1 := covariance_hasSum u hu ((star A : Op) v) ((star A : Op) w)
  have h2 := covariance_hasSum (fun i => A (u i)) (image_summable A u hu) v w
  have he (i : ℕ) : inner ℂ ((star A : Op) v) (u i)*inner ℂ (u i) ((star A : Op) w)=
      inner ℂ v (A (u i))*inner ℂ (A (u i)) w := by
    have hl : inner ℂ ((star A : Op) v) (u i)=inner ℂ v (A (u i)) := A.adjoint_inner_left _ _
    have hr : inner ℂ (u i) ((star A : Op) w)=inner ℂ (A (u i)) w := A.adjoint_inner_right _ _
    rw [hl,hr]
  simp_rw [he] at h1
  have hh := h1.unique h2
  change inner ℂ v (A (covariance u ((star A : Op) w)))=_
  exact (A.adjoint_inner_left _ _).symm.trans hh

/-- The project diagonal trace is cyclic for a density and a supported isometry.
Absolute summability comes from the square-root columns. -/
theorem isometry_trace {P} (R : NormalRealization P) (A : Op)
    (hA : star A*A=R.support) :
    trace (A*R.density.op*star A)=trace R.density.op := by
  let u := rootFamily R.density
  have hu := root_summable R.density
  have hepos : Positive R.support := by
    have hh := ContinuousLinearMap.isPositive_adjoint_comp_self R.support
    change Positive (star R.support*R.support) at hh
    simpa only [R.support_projection.1,R.support_projection.2] using hh
  have h1 := covariance_mul_trace (fun i => A (u i)) (image_summable A u hu)
    1 ContinuousLinearMap.isPositive_one
  have h2 := covariance_mul_trace u hu R.support hepos
  have hi (i : ℕ) : inner ℂ (A (u i)) (A (u i))=inner ℂ (R.support (u i)) (u i) := by
    calc
      _ = inner ℂ (u i) ((star A*A) (u i)) := A.adjoint_inner_right _ _ |>.symm
      _ = inner ℂ (u i) (R.support (u i)) := by rw [hA]
      _ = _ := hepos.isSymmetric _ _ |>.symm
  calc
    _ = trace (covariance (fun i => A (u i))) := by
      rw [density_eq_covariance,covariance_map _ (root_summable _) A]
    _ = ∑' i,inner ℂ (A (u i)) (A (u i)) := by simpa only [mul_one,one_apply_eq_self] using h1.2.1
    _ = ∑' i,inner ℂ (R.support (u i)) (u i) := tsum_congr hi
    _ = trace (R.density.op*R.support) := by
      rw [density_eq_covariance]
      exact h2.2.1.symm
    _ = _ := by rw [density_support_right R]

/-- Density products have a summable diagonal for every positive factor. -/
theorem density_diagonal (h : Density) (B : Op) (hB : Positive B) :
    Summable (fun i => entry (h.op*B) i i) := by
  rw [density_eq_covariance]
  exact (covariance_mul_trace _ (root_summable h) B hB).1

/-- Finite additivity is used only for density products with summable diagonals. -/
theorem trace_density_sum {ι : Type} (h : Density) (s : Finset ι) (B : ι → Op)
    (hB : ∀ i ∈ s,Positive (B i)) :
    trace (h.op*∑ i ∈ s,B i)=∑ i ∈ s,trace (h.op*B i) := by
  classical
  simp only [Finset.mul_sum,trace,entry,ContinuousLinearMap.sum_apply,lp.coeFn_sum,
    Finset.sum_apply]
  exact (Summable.tsum_finsetSum (fun i hi => density_diagonal h (B i) (hB i hi)))

/-- The trace-one normalization in the original diagonal convention. -/
theorem trace_density_re (h : Density) : (trace h.op).re=1 := by
  let u := rootFamily h
  have hu := root_summable h
  have ht := covariance_mul_trace u hu 1 ContinuousLinearMap.isPositive_one
  have hh := ht.2.2.hasSum.mapL Complex.reCLM
  have hm := covariance_trace u hu
  have he : (∑' i, ‖u i‖^2)=1 := by
    rw [← hm.2]
    change (∑' a,(entry (covariance (rootFamily h)) a a).re)=1
    rw [← density_eq_covariance h]
    exact h.trace_one
  have hi (i : ℕ) : (inner ℂ ((1:Op) (u i)) (u i)).re=‖u i‖^2 := by
    change (inner ℂ (u i) (u i)).re=_
    exact inner_self_eq_norm_sq (𝕜 := ℂ) _
  change HasSum (fun i => (inner ℂ ((1:Op) (u i)) (u i)).re)
    (∑' i,inner ℂ ((1:Op) (u i)) (u i)).re at hh
  simp_rw [hi] at hh
  have hh' := hh.tsum_eq.symm.trans he
  simpa only [← ht.2.1,mul_one,u,← density_eq_covariance h] using hh'

/-- The exact three-quarter root mass does not need the full word partition. -/
theorem root_mass {P} (hP : P.admissible) (R : NormalRealization P) :
    (trace (R.density.op*R.label P.root)).re=3/4 := by
  have hp := root_projection hP R
  have hpos (Q : Op) (hQ : Projection Q) : Positive Q := by
    have hh := ContinuousLinearMap.isPositive_adjoint_comp_self Q
    change Positive (star Q*Q) at hh
    simpa only [hQ.1,hQ.2] using hh
  have htrace (a : Fin 4) : trace (R.density.op*(R.creation a*star (R.creation a)))=
      (1/16:ℂ)*trace R.density.op := by
    rw [← mul_assoc,R.modular a,smul_mul_assoc,CompilerAlgebra.trace_smul,
      isometry_trace R _ (by simpa using R.isometries a a)]
  have ht : trace (R.density.op*(R.support-R.label P.root))=
      (1/4:ℂ)*trace R.density.op := by
    rw [← R.ranges,trace_density_sum]
    · simp_rw [htrace]
      simp
      ring
    · intro a _
      exact ContinuousLinearMap.isPositive_self_comp_adjoint _
  have hsub : trace (R.density.op*(R.support-R.label P.root))=
      trace R.density.op-trace (R.density.op*R.label P.root) := by
    rw [mul_sub]
    change (∑' i, (entry (R.density.op*R.support) i i-entry (R.density.op*R.label P.root) i i))=_
    rw [(density_diagonal _ _ (hpos _ R.support_projection)).tsum_sub
      (density_diagonal _ _ (hpos _ hp)),density_support_right R]
    rfl
  rw [hsub] at ht
  have hr := congrArg Complex.re ht
  have hn := trace_density_re R.density
  norm_num [Complex.mul_re] at hr
  linarith

#print axioms covariance_map
#print axioms isometry_trace
#print axioms root_mass
end Sigma2.FockTrace