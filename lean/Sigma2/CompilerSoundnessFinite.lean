import Sigma2.CompilerSoundnessFinalExtraction

/-! Finite support of the actual extracted source, with no change of strategy. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessFinite
open Preliminaries Coefficients CompilerSoundnessExtraction
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
  CompilerSoundnessSource.support

theorem finite_marginal_support {s : Scenario} (S : PureStrategy s) (d : ℕ)
    (hfin : FiniteSupport S d) (h : Density) (hm : MarginalA (normalOfPure S) h)
    (e : Op) (he : SupportOf h e) : FiniteDimensional ℂ (LinearMap.range e.toLinearMap) := by
  let f : Fin d → H := fun j => column S.vector j.val
  let V := Submodule.span ℂ (Set.range f)
  letI : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  have hcol (j : ℕ) : column S.vector j ∈ V := by
    by_cases hj : j<d
    · exact Submodule.subset_span ⟨⟨j,hj⟩,rfl⟩
    · have hz : column S.vector j=0 := by
        ext i
        exact hfin i j (Or.inr (by omega))
      rw [hz]
      exact V.zero_mem
  have hc : (1-V.starProjection)*e=0 := by
    apply PureSupport.columns_zero_support S h hm e he
    intro j
    change column S.vector j-V.starProjection (column S.vector j)=0
    rw [(Submodule.starProjection_eq_self_iff).mpr (hcol j),sub_self]
  have hproj : V.starProjection*e=e := by
    rw [sub_mul,one_mul] at hc
    exact (sub_eq_zero.mp hc).symm
  have hle : LinearMap.range e.toLinearMap≤V := by
    rintro v ⟨w,hw⟩
    have hh := congrArg (fun A : Op => A w) hproj
    change V.starProjection (e w)=e w at hh
    have hv : e w=v := hw
    exact hv ▸ (Submodule.starProjection_eq_self_iff.mp hh)
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

theorem finite_source (P : Presentation) (S : PureStrategy (CompilerScaffold.finalGame P).scenario)
    (d : ℕ) (hfin : FiniteSupport S d) (E : SupportedScaffold P)
    (hv : E.strategy.vector=(normalOfPure S).vector)
    (hw : E.strategy.weight=(normalOfPure S).weight) :
    FiniteDimensional ℂ (LinearMap.range (CompilerSoundnessSource.support E).toLinearMap) := by
  have hm : MarginalA (normalOfPure S) E.densityA :=
    (CompilerSoundnessFinalExtraction.marginal_preserved _ _ hv hw _).mp E.marginalA
  letI := finite_marginal_support S d hfin E.densityA hm E.supportA E.supportA_laws
  have hle : LinearMap.range (CompilerSoundnessSource.support E).toLinearMap≤
      LinearMap.range E.supportA.toLinearMap := by
    rintro v ⟨w,hw⟩
    refine ⟨CompilerSoundnessSource.support E w,?_⟩
    have hv : CompilerSoundnessSource.support E w=v := hw
    change E.supportA (CompilerSoundnessSource.support E w)=v
    exact (congrArg (fun A : Op => A w) (CompilerSoundnessSource.source_supported E).1).trans hv
  exact FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

#print axioms finite_marginal_support
#print axioms finite_source
end Sigma2.CompilerSoundnessFinite
