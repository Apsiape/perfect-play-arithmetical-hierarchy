import Sigma2.TreeFoundation
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section
set_option maxHeartbeats 500000
open scoped BigOperators
namespace Sigma2.FinitePhaseSector

/-- The three centralizer unitaries needed by the finite Weyl argument. -/
structure Triple {P} (R : NormalRealization P) where
  j : Op
  k : Op
  z : Op
  unitary : ∀ T ∈ [j,k,z], TypedAt R.support T .unitary
  supported : ∀ T ∈ [j,k,z], R.support*T=T ∧ T*R.support=T
  centralizer : ∀ T ∈ [j,k,z], Centralizes R.density.op T
  weyl : j*k=z*k*j
  central_phase : ∀ T ∈ [j,k], z*T=T*z
  creation_commute : ∀ a,j*R.creation a=R.creation a*j ∧
    k*R.creation a=R.creation a*k ∧ z*R.creation a=R.creation a*z

/-- A nonzero finite density block supplies an actual scalar-phase Weyl sector.
The clock module applies its already-proved determinant identity to these matrices. -/
theorem sector {P} (hP : P.admissible) (R : NormalRealization P) (D : Triple R) :
    ∃ (d : ℕ) (ζ : ℂ) (ξ : H) (J K : Matrix (Fin d) (Fin d) ℂ),
      0<d ∧ ξ≠0 ∧ R.label P.root ξ=ξ ∧ D.z ξ=ζ • ξ ∧
      J*K=ζ • (K*J) ∧ (K*J).det≠0 := by  classical
  obtain ⟨μ,v,hμ,hv,hdv,hpv⟩ := TreeFoundation.root_density_block hP R
  letI := DensitySpectral.finite_block R.density μ hμ
  let E := DensitySpectral.block R.density μ ⊓
    Module.End.eigenspace (R.label P.root).toLinearMap 1
  have hve : v ∈ E := ⟨Module.End.mem_eigenspace_iff.mpr hdv,
    Module.End.mem_eigenspace_iff.mpr (by change R.label P.root v=1 • v; rw [one_smul]; exact hpv)⟩
  letI : Nontrivial E := ⟨⟨⟨v,hve⟩,0,fun h => hv (congrArg Subtype.val h)⟩⟩
  have hroot (u : E) : R.label P.root u=(u : H) := by
    have hh := Module.End.mem_eigenspace_iff.mp u.property.2
    change R.label P.root u=1 • (u : H) at hh
    simpa only [one_smul] using hh
  have hsup (u : E) : R.support u=(u : H) := by
    rw [← hroot u]
    exact congrArg (fun T : Op => T u) (R.label_supported P.root).1
  have hinvariant (T : Op) (hT : T ∈ [D.j,D.k,D.z]) (u : E) : T u ∈ E := by
    have hun : TypedAt R.support T .unitary := D.unitary T hT
    have hsu := D.supported T hT
    have hcomm : ∀ a,T*R.creation a=R.creation a*T := by
      rcases List.mem_cons.mp hT with he | ht
      · subst T; exact fun a => (D.creation_commute a).1
      · rcases List.mem_cons.mp ht with he | ht
        · subst T; exact fun a => (D.creation_commute a).2.1
        · have he : T=D.z := by simpa using ht
          subst T; exact fun a => (D.creation_commute a).2.2
    have hr := TreeFoundation.unitary_commutes_root R T hun hsu hcomm
    refine ⟨DensitySpectral.block_invariant R.density T
      (D.centralizer T hT) μ u u.property.1,?_⟩
    apply Module.End.mem_eigenspace_iff.mpr
    change R.label P.root (T u)=1 • T u
    rw [one_smul]
    calc
      _ = T (R.label P.root u) := congrArg (fun A : Op => A u) hr.symm
      _ = T u := by rw [hroot]
  let ZE : Module.End ℂ E :=
    (D.z.toLinearMap.domRestrict E).codRestrict E (hinvariant D.z (by simp))
  let JE : Module.End ℂ E :=
    (D.j.toLinearMap.domRestrict E).codRestrict E (hinvariant D.j (by simp))
  let KE : Module.End ℂ E :=
    (D.k.toLinearMap.domRestrict E).codRestrict E (hinvariant D.k (by simp))
  obtain ⟨ζ,hζ⟩ := ZE.exists_eigenvalue
  obtain ⟨u,hu⟩ := hζ.exists_hasEigenvector
  let F := Module.End.eigenspace ZE ζ
  letI : Nontrivial F := ⟨⟨⟨u,hu.1⟩,0,fun h => hu.2 (congrArg Subtype.val h)⟩⟩
  have hJF (t : F) : JE t ∈ F := by
    apply Module.End.mem_eigenspace_iff.mpr
    apply Subtype.ext
    change D.z (D.j t)=ζ • D.j t
    have he := Module.End.mem_eigenspace_iff.mp t.property
    have he' : D.z (t : E)=ζ • (t : E) := congrArg (fun x : E => (x : H)) he
    calc
      _ = D.j (D.z t) := congrArg (fun A : Op => A (t : E)) (D.central_phase D.j (by simp))
      _ = _ := by rw [he',map_smul]
  have hKF (t : F) : KE t ∈ F := by
    apply Module.End.mem_eigenspace_iff.mpr
    apply Subtype.ext
    change D.z (D.k t)=ζ • D.k t
    have he := Module.End.mem_eigenspace_iff.mp t.property
    have he' : D.z (t : E)=ζ • (t : E) := congrArg (fun x : E => (x : H)) he
    calc
      _ = D.k (D.z t) := congrArg (fun A : Op => A (t : E)) (D.central_phase D.k (by simp))
      _ = _ := by rw [he',map_smul]
  let JF : Module.End ℂ F := (JE.domRestrict F).codRestrict F hJF
  let KF : Module.End ℂ F := (KE.domRestrict F).codRestrict F hKF
  have hji : Function.Injective JF := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact TreeFoundation.unitary_injective_on_support R D.j (D.unitary D.j (by simp))
      _ _ (hsup _) (hsup _) (congrArg (fun x : F => ((x : E) : H)) he)
  have hki : Function.Injective KF := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact TreeFoundation.unitary_injective_on_support R D.k (D.unitary D.k (by simp))
      _ _ (hsup _) (hsup _) (congrArg (fun x : F => ((x : E) : H)) he)
  have hweyl : JF*KF=ζ • (KF*JF) := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    apply Subtype.ext
    change D.j (D.k t)=ζ • D.k (D.j t)
    have he := Module.End.mem_eigenspace_iff.mp (KF (JF t)).property
    have he' : D.z (D.k (D.j t))=ζ • D.k (D.j t) :=
      congrArg (fun x : E => (x : H)) he
    calc
      _ = D.z (D.k (D.j t)) := congrArg (fun A : Op => A ((t : E) : H)) D.weyl
      _ = _ := he'
  letI : FiniteDimensional ℂ F := inferInstance
  letI : Module.Free ℂ F := Module.Free.of_divisionRing ℂ F
  let b := Module.finBasis ℂ F
  let τ := LinearMap.toMatrixAlgEquiv b
  have hmatrix : τ JF*τ KF=ζ • (τ KF*τ JF) := by
    simpa only [map_mul,map_smul] using congrArg τ hweyl
  let M : Module.End ℂ F := KF*JF
  have hinj : Function.Injective M := hki.comp hji
  have hsurj : Function.Surjective M := @LinearMap.surjective_of_injective ℂ F _ _ _ _ M hinj
  let e := LinearEquiv.ofBijective M ⟨hinj,hsurj⟩
  let L := e.symm.toLinearMap
  have hleft : L*(KF*JF)=1 := by
    apply LinearMap.ext
    intro t
    exact e.symm_apply_apply t
  have hleftmat : τ L*(τ KF*τ JF)=1 := by
    calc
      _ = τ (L*(KF*JF)) := by simp only [map_mul]
      _ = 1 := by rw [hleft,map_one]
  have hdet : (τ KF*τ JF).det≠0 := by
    have hh := congrArg Matrix.det hleftmat
    rw [Matrix.det_mul,Matrix.det_one] at hh
    intro hz
    rw [hz,mul_zero] at hh
    exact zero_ne_one hh
  refine ⟨Module.finrank ℂ F,ζ,(u : H),τ JF,τ KF,(Module.finrank_pos (R := ℂ) (M := F)),?_,hroot u,?_,hmatrix,hdet⟩
  · intro he
    apply hu.2
    exact Subtype.ext he
  · exact congrArg (fun x : E => (x : H)) hu.apply_eq_smul

#print axioms sector
end Sigma2.FinitePhaseSector