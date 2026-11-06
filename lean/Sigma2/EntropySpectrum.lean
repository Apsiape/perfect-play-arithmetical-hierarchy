import Sigma2.EntropyEnumeration
import Mathlib.Basic.Denumerable

set_option synthInstance.maxHeartbeats 10000
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.EntropySpectrum

def eigIndex (h : Density) (μ : ℂ) : Set (DensitySpectral.block h μ) :=
  Classical.choose (exists_hilbertBasis ℂ (DensitySpectral.block h μ))

def eigBasis (h : Density) (μ : ℂ) : HilbertBasis (eigIndex h μ) ℂ (DensitySpectral.block h μ) :=
  Classical.choose (Classical.choose_spec (exists_hilbertBasis ℂ (DensitySpectral.block h μ)))

abbrev Index (h : Density) := Σ μ : ℂ, eigIndex h μ

def vector (h : Density) (a : Index h) : H := (eigBasis h a.1 a.2 : H)

lemma vector_orthonormal (h : Density) : Orthonormal ℂ (vector h) := by
  classical
  constructor
  · intro a
    exact (eigBasis h a.1).orthonormal.norm_eq_one a.2
  · rintro ⟨μ, a⟩ ⟨ν, b⟩ hab
    by_cases hμ : μ = ν
    · subst ν
      apply (eigBasis h μ).orthonormal.inner_eq_zero
      intro heq
      exact hab (congrArg (Sigma.mk μ) heq)
    · have hf := h.positive.isSymmetric.orthogonalFamily_eigenspaces
      exact hf hμ (eigBasis h μ a) (eigBasis h ν b)

lemma vector_total (h : Density) : (Submodule.span ℂ (Set.range (vector h)))ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have hx' : x ∈ (⨆ μ, DensitySpectral.block h μ)ᗮ := by
    rw [← Submodule.iInf_orthogonal]
    simp only [Submodule.mem_iInf]
    intro μ
    rw [Submodule.mem_orthogonal']
    intro y hy
    have hs := (((eigBasis h μ).hasSum_repr ⟨y, hy⟩).mapL
      (DensitySpectral.block h μ).subtypeL).mapL (innerSL ℂ x)
    have hz (a : eigIndex h μ) : inner ℂ x (eigBasis h μ a : H) = 0 :=
      (Submodule.span ℂ (Set.range (vector h))).inner_left_of_mem_orthogonal
        (Submodule.subset_span ⟨⟨μ,a⟩, rfl⟩) hx
    have hs0 : HasSum (fun _ : eigIndex h μ => (0 : ℂ)) (inner ℂ x y) := by
      simpa only [innerSL_apply_apply, map_smul, Submodule.subtypeL_apply,
        inner_smul_right, hz, mul_zero, smul_zero] using hs
    exact hs0.unique hasSum_zero
  simpa only [DensitySpectral.blocks_total h] using hx'

def fullBasis (h : Density) : HilbertBasis (Index h) ℂ H :=
  HilbertBasis.mkOfOrthogonalEqBot (vector_orthonormal h) (vector_total h)

lemma fullBasis_eq (h : Density) : (fullBasis h : Index h → H) = vector h :=
  HilbertBasis.coe_mkOfOrthogonalEqBot (vector_orthonormal h) (vector_total h)

local instance : TopologicalSpace.SeparableSpace H := by
  let B0 : HilbertBasis ℕ ℂ H := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)
  have hs := ((Set.countable_range B0).isSeparable.span (R := ℂ)).closure
  apply TopologicalSpace.isSeparable_univ_iff.mp
  simpa only [← Submodule.topologicalClosure_coe, B0.dense_span, Submodule.top_coe] using hs

lemma index_countable (h : Density) : Countable (Index h) :=
  Coefficients.orthonormal_countable (vector_orthonormal h)

lemma index_infinite (h : Density) : Infinite (Index h) := by
  classical
  by_contra hn
  letI : Finite (Index h) := not_infinite_iff_finite.mp hn
  letI : Fintype (Index h) := Fintype.ofFinite (Index h)
  letI : FiniteDimensional ℂ H := Module.Finite.of_basis (fullBasis h).toOrthonormalBasis.toBasis
  let B0 : HilbertBasis ℕ ℂ H := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)
  exact Module.Finite.not_linearIndependent_of_infinite B0 B0.orthonormal.linearIndependent

lemma vector_eigen (h : Density) (a : Index h) : h.op (vector h a) = a.1 • vector h a :=
  Module.End.mem_eigenspace_iff.mp (eigBasis h a.1 a.2).property

lemma eigen_real (h : Density) (a : Index h) : (a.1.re : ℂ) = a.1 := by
  apply RCLike.conj_eq_iff_re.mp
  apply h.positive.isSymmetric.conj_eigenvalue_eq_self
  apply Module.End.hasEigenvalue_of_hasEigenvector
  exact ⟨Module.End.mem_eigenspace_iff.mpr (vector_eigen h a),
    (vector_orthonormal h).ne_zero a⟩

/-- The compact spectral theorem, with a Hilbert basis in each eigenspace,
produces a countable complete eigenfamily including the kernel. -/
theorem exists_hilbert_eigenbasis (h : Density) :
    ∃ (b : HilbertBasis ℕ ℂ H) (q : ℕ → ℝ),
      (∀ i, 0 ≤ q i) ∧ ∀ i, h.op (b i) = (q i : ℂ) • b i := by
  classical
  letI := index_countable h
  letI := index_infinite h
  let e : ℕ ≃ Index h := Classical.choice (inferInstance : Nonempty (ℕ ≃ Index h))
  have hrange : Set.range (vector h ∘ e) = Set.range (vector h) := by
    ext x
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨e n, rfl⟩
    · rintro ⟨a, rfl⟩; exact ⟨e.symm a, by simp⟩
  have hvN := (vector_orthonormal h).comp e e.injective
  have htN : (Submodule.span ℂ (Set.range (vector h ∘ e)))ᗮ = ⊥ := by
    rw [hrange]; exact vector_total h
  let BN := HilbertBasis.mkOfOrthogonalEqBot hvN htN
  have hBN (n : ℕ) : BN n = vector h (e n) :=
    congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot hvN htN) n
  refine ⟨BN, fun n => (e n).1.re, ?_, ?_⟩
  · intro n
    change 0 ≤ (e n).1.re
    apply eigenvalue_nonneg_of_nonneg (𝕜 := ℂ)
      (Module.End.hasEigenvalue_of_hasEigenvector (x := vector h (e n)) ⟨?_,
        (vector_orthonormal h).ne_zero (e n)⟩)
      (fun x => h.positive.re_inner_nonneg_right x)
    apply Module.End.mem_eigenspace_iff.mpr
    exact (vector_eigen h (e n)).trans
      (congrArg (fun z : ℂ => z • vector h (e n)) (eigen_real h (e n)).symm)
  · intro n
    change h.op (BN n) = ((e n).1.re : ℂ) • BN n
    rw [hBN]
    exact (vector_eigen h (e n)).trans
      (congrArg (fun z : ℂ => z • vector h (e n)) (eigen_real h (e n)).symm)

#print axioms exists_hilbert_eigenbasis
end Sigma2.EntropySpectrum
