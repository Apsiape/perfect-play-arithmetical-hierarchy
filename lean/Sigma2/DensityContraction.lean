import Sigma2.DensitySpectral
import Sigma2.FiniteContraction

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.DensityContraction
open DensitySpectral

/-- The eigenspaces form an actual Hilbert direct sum, including the zero block. -/
def decomposition (h : Density) :
    IsHilbertSum ℂ (fun μ => ↥(block h μ)) (fun μ => (block h μ).subtypeₗᵢ) := by
  apply IsHilbertSum.mkInternal (block h) h.positive.isSymmetric.orthogonalFamily_eigenspaces
  rw [← Submodule.orthogonal_orthogonal_eq_closure,blocks_total h]
  simp

/-- Assemble arbitrary unitary choices on the density blocks. -/
theorem assemble (h : Density) (W : ∀ μ : ℂ, block h μ ≃ₗᵢ[ℂ] block h μ) :
    ∃ U : H ≃ₗᵢ[ℂ] H, ∀ μ (v : block h μ), U v=(W μ v : H) := by
  let V : ∀ μ : ℂ, block h μ →ₗᵢ[ℂ] H :=
    fun μ => (block h μ).subtypeₗᵢ.comp (W μ).toLinearIsometry
  have ho : OrthogonalFamily ℂ (fun μ => ↥(block h μ)) V := by
    intro μ ν hμν v w
    exact h.positive.isSymmetric.orthogonalFamily_eigenspaces hμν (W μ v) (W ν w)
  have hr (μ : ℂ) : LinearMap.range (V μ).toLinearMap=block h μ := by
    ext v
    constructor
    · rintro ⟨w,rfl⟩
      exact (W μ w).property
    · intro hv
      exact ⟨(W μ).symm ⟨v,hv⟩,congrArg Subtype.val ((W μ).apply_symm_apply ⟨v,hv⟩)⟩
  have hd : IsHilbertSum ℂ (fun μ => ↥(block h μ)) V := by
    apply IsHilbertSum.mk ho
    simp_rw [hr]
    rw [← Submodule.orthogonal_orthogonal_eq_closure,blocks_total h]
    simp
  let U := (decomposition h).linearIsometryEquiv.trans hd.linearIsometryEquiv.symm
  refine ⟨U,?_⟩
  intro μ v
  have he := (decomposition h).linearIsometryEquiv_symm_apply_single v
  change (decomposition h).linearIsometryEquiv.symm (lp.single 2 μ v)=(v : H) at he
  have hh : (decomposition h).linearIsometryEquiv (v : H)=lp.single 2 μ v := by
    rw [← he]
    exact (decomposition h).linearIsometryEquiv.apply_symm_apply _
  change hd.linearIsometryEquiv.symm ((decomposition h).linearIsometryEquiv v)=_
  rw [hh,hd.linearIsometryEquiv_symm_apply_single]
  rfl

/-- Equality of bounded maps can be checked on the density eigenspaces. -/
theorem ext_blocks (h : Density) (A B : Op)
    (he : ∀ μ (v : block h μ), A v=B v) : A=B := by
  have hk : (⨆ μ, block h μ).topologicalClosure ≤ LinearMap.ker (A-B).toLinearMap := by
    apply Submodule.topologicalClosure_minimal
    · apply iSup_le
      intro μ v hv
      change A v-B v=0
      exact sub_eq_zero.mpr (he μ ⟨v,hv⟩)
    · exact ContinuousLinearMap.isClosed_ker (A-B)
  have ht : (⨆ μ, block h μ).topologicalClosure=⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure,blocks_total h]
    simp
  rw [ht] at hk
  apply ContinuousLinearMap.ext
  intro v
  have hh := hk (Submodule.mem_top (x:=v))
  change A v-B v=0 at hh
  exact sub_eq_zero.mp hh

/-- A blockwise operator commutes with the density because the density is scalar
on each block. -/
theorem centralizes_of_blocks (h : Density) (A : Op)
    (hi : ∀ μ (v : block h μ), A v ∈ block h μ) : Centralizes h.op A := by
  apply ext_blocks h
  intro μ v
  have hv := v.property
  have ha := hi μ v
  rw [Module.End.mem_eigenspace_iff] at hv ha
  change h.op v=μ • (v : H) at hv
  change h.op (A v)=μ • A v at ha
  change h.op (A v)=A (h.op v)
  rw [hv,map_smul,ha]

/-- Unitary operators and onto isometries are interchangeable on each block. -/
def unitaryEquiv {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : unitary (E →L[ℂ] E)) : E ≃ₗᵢ[ℂ] E := by
  let A : E →L[ℂ] E := U
  have hl : star A*A=1 := U.property.1
  have hr : A*star A=1 := U.property.2
  let L : E →ₗᵢ[ℂ] E :=
    { toLinearMap := A.toLinearMap
      norm_map' := by
        intro v
        have hi : Isometry A := A.isometry_iff_adjoint_comp_self.mpr hl
        change ‖A v‖=‖v‖
        exact hi.norm_map_of_map_zero (map_zero A) v }
  apply LinearIsometryEquiv.ofSurjective L
  intro v
  refine ⟨star A v,?_⟩
  exact congrArg (fun B : E →L[ℂ] E => B v) hr

/-- The exact two-unitary encoding on the faithful normal density. -/
theorem mean (h : Density) (hf : Faithful h) (T : Op)
    (hT : Contraction T) (hc : Centralizes h.op T) :
    ∃ U V : Op, Unitary U ∧ Unitary V ∧ Centralizes h.op U ∧ Centralizes h.op V ∧
      T=(1/2:ℂ) • (U+V) := by
  have hfin (μ : ℂ) : FiniteDimensional ℂ (block h μ) := by
    by_cases hz : μ=0
    · subst μ
      rw [zero_block h hf]
      infer_instance
    · exact finite_block h μ hz
  let Tμ (μ : ℂ) : block h μ →L[ℂ] block h μ :=
    T.restrict (fun v hv => block_invariant h T hc μ v hv)
  have hn (μ : ℂ) : ‖Tμ μ‖ ≤ 1 := by
    apply (Tμ μ).opNorm_le_bound (by norm_num)
    intro v
    change ‖T v‖ ≤ 1*‖(v : H)‖
    exact (T.le_opNorm v).trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  have hm (μ : ℂ) : ∃ U V : unitary (block h μ →L[ℂ] block h μ),
      Tμ μ=(1/2:ℂ) • ((U : block h μ →L[ℂ] block h μ)+V) := by
    letI := hfin μ
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
    rw [show A v=((Uμ μ : block h μ →L[ℂ] block h μ) v : H) from hU μ v,show B v=((Vμ μ : block h μ →L[ℂ] block h μ) v : H) from hV μ v]
    exact hh

#print axioms mean
end Sigma2.DensityContraction

