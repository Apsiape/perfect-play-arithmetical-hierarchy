import Sigma2.DensityContraction

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace Sigma2.SupportedContraction
open DensitySpectral DensityContraction

/-- The same construction works when the contraction vanishes on the kernel
of a nonfaithful density: the infinite zero block has the explicit mean (I,-I). -/
theorem mean_of_kernel_zero (h : Density) (T : Op) (hT : Contraction T)
    (hc : Centralizes h.op T) (hk : ∀ v, h.op v=0 → T v=0) :
    ∃ U V : Op, Unitary U ∧ Unitary V ∧ Centralizes h.op U ∧ Centralizes h.op V ∧
      T=(1/2:ℂ) • (U+V) := by
  let Tμ (μ : ℂ) : block h μ →L[ℂ] block h μ :=
    T.restrict (fun v hv => block_invariant h T hc μ v hv)
  have hn (μ : ℂ) : ‖Tμ μ‖ ≤ 1 := by
    apply (Tμ μ).opNorm_le_bound (by norm_num)
    intro v
    change ‖T v‖ ≤ 1*‖(v : H)‖
    exact (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  have hm (μ : ℂ) : ∃ U V : unitary (block h μ →L[ℂ] block h μ),
      Tμ μ=(1/2:ℂ) • ((U : block h μ →L[ℂ] block h μ)+V) := by
    by_cases hz : μ=0
    · subst μ
      have ht : Tμ 0=0 := by
        apply ContinuousLinearMap.ext
        intro v
        apply Subtype.ext
        change T v=0
        apply hk
        have hh := v.property
        rw [Module.End.mem_eigenspace_iff] at hh
        change h.op v=(0:ℂ) • (v : H) at hh
        simpa only [zero_smul] using hh
      let L : block h 0 ≃ₗᵢ[ℂ] block h 0 := LinearIsometryEquiv.neg ℂ
      let N : unitary (block h 0 →L[ℂ] block h 0) :=
        ⟨L.toLinearIsometry.toContinuousLinearMap,
          FiniteContraction.isometry_unitary _ L.surjective⟩
      refine ⟨1,N,?_⟩
      rw [ht]
      apply ContinuousLinearMap.ext
      intro v
      change (0 : block h 0)=(1/2:ℂ) • (v + -v)
      rw [add_neg_cancel,smul_zero]
    · letI := finite_block h μ hz
      exact FiniteContraction.finite_mean (Tμ μ) (hn μ)
  choose Uμ Vμ hμ using hm
  obtain ⟨U,hU⟩ := assemble h (fun μ => unitaryEquiv (Uμ μ))
  obtain ⟨V,hV⟩ := assemble h (fun μ => unitaryEquiv (Vμ μ))
  let A := U.toLinearIsometry.toContinuousLinearMap
  let B := V.toLinearIsometry.toContinuousLinearMap
  have ha : A ∈ unitary Op := FiniteContraction.isometry_unitary _ U.surjective
  have hb : B ∈ unitary Op := FiniteContraction.isometry_unitary _ V.surjective
  refine ⟨A,B,ha,hb,?_,?_,?_⟩
  · apply centralizes_of_blocks
    intro μ v
    rw [show A v=((Uμ μ : block h μ →L[ℂ] block h μ) v : H) from hU μ v]
    exact ((Uμ μ : block h μ →L[ℂ] block h μ) v).property
  · apply centralizes_of_blocks
    intro μ v
    rw [show B v=((Vμ μ : block h μ →L[ℂ] block h μ) v : H) from hV μ v]
    exact ((Vμ μ : block h μ →L[ℂ] block h μ) v).property
  · apply ext_blocks h
    intro μ v
    have hh := congrArg (fun C : block h μ →L[ℂ] block h μ => (C v : H)) (hμ μ)
    change T v=(1/2:ℂ) • (A v+B v)
    rw [show A v=((Uμ μ : block h μ →L[ℂ] block h μ) v : H) from hU μ v,
      show B v=((Vμ μ : block h μ →L[ℂ] block h μ) v : H) from hV μ v]
    exact hh

/-- Proper supports, including finite-dimensional source corners, do not need
a globally faithful density on the fixed infinite-dimensional ambient model. -/
theorem supported_mean (h : Density) (e : Op) (he : Projection e) (hs : e*h.op=h.op)
    (hf : ∀ v,e v=v → h.op v=0 → v=0) (T : Op) (hT : Contraction T)
    (hc : Centralizes h.op T) (ht : T*e=T) :
    ∃ U V : Op, Unitary U ∧ Unitary V ∧ Centralizes h.op U ∧ Centralizes h.op V ∧
      T=(1/2:ℂ) • (U+V) := by
  apply mean_of_kernel_zero h T hT hc
  intro v hv
  have hright : h.op*e=h.op := by
    have hh := congrArg star hs
    simpa only [star_mul,he.1,h.positive.isSelfAdjoint.star_eq] using hh
  have hev : e v=0 := by
    apply hf
    · exact congrArg (fun A : Op => A v) he.2
    · change (h.op*e) v=0
      rw [hright,hv]
  calc
    T v = T (e v) := congrArg (fun A : Op => A v) ht.symm
    _ = 0 := by rw [hev,map_zero]

#print axioms mean_of_kernel_zero
#print axioms supported_mean
end Sigma2.SupportedContraction
