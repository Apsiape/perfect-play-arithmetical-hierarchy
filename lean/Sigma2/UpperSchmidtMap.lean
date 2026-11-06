import Sigma2.UpperPOVMTransport
import Sigma2.UpperDiagonalVectors

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.UpperSchmidtMap
open UpperSchmidtSpectrum UpperSchmidtOperators

@[simp] theorem embed_single {ι : Type} [DecidableEq ι] (f : ι ↪ ℕ) (i : ι) (c : ℂ) :
    Coefficients.embed f (lp.single 2 i c)=c • basis (f i) := by
  rw [Coefficients.embed,OrthogonalFamily.linearIsometry_apply_single,LinearIsometry.toSpanSingleton_apply]
  congr 1
  change (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)) (f i)=basis (f i)
  rw [← HilbertBasis.repr_symm_single]
  change (LinearIsometryEquiv.refl ℂ H).symm (lp.single 2 (f i) 1)=basis (f i)
  ext k
  simp [LinearIsometryEquiv.refl,LinearIsometryEquiv.symm,basis,lp.single_apply]

abbrev PositiveIndex (q : ℕ → ℝ) := {i : ℕ // 0<q i}

def inclusion (q : ℕ → ℝ) : lp (fun _ : PositiveIndex q => ℂ) 2 →ₗᵢ[ℂ] H :=
  Coefficients.embed ⟨Subtype.val,Subtype.val_injective⟩

@[simp] theorem inclusion_single (q : ℕ → ℝ) (i : PositiveIndex q) (c : ℂ) :
    inclusion q (lp.single 2 i c)=c • basis i.val := embed_single _ i c

theorem inclusion_adjoint_coordinate (q : ℕ → ℝ) (w : H) (i : PositiveIndex q) :
    (inclusion q).toContinuousLinearMap.adjoint w i=w i.val := by
  have hh := ContinuousLinearMap.adjoint_inner_right (inclusion q).toContinuousLinearMap (lp.single 2 i 1) w
  change inner ℂ (lp.single 2 i 1) ((inclusion q).toContinuousLinearMap.adjoint w)=inner ℂ (inclusion q (lp.single 2 i 1)) w at hh
  rw [inclusion_single,one_smul] at hh
  simpa only [basis,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using hh

def bobIsometry (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) :
    lp (fun _ : PositiveIndex q => ℂ) 2 →ₗᵢ[ℂ] H :=
  (bobVector_orthonormal v hv q u hu he).orthogonalFamily.linearIsometry

@[simp] theorem bobIsometry_single (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i)
    (i : PositiveIndex q) (c : ℂ) :
    bobIsometry v hv q u hu he (lp.single 2 i c)=c • bobVector v q u i.val := by
  rw [bobIsometry,OrthogonalFamily.linearIsometry_apply_single]
  rfl

def bobMap (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) : Op :=
  (bobIsometry v hv q u hu he).toContinuousLinearMap.comp (inclusion q).toContinuousLinearMap.adjoint

theorem bobMap_basis (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) (i : ℕ) :
    bobMap v hv q u hu he (basis i)=bobVector v q u i := by
  by_cases hi : 0<q i
  · have hj : (inclusion q).toContinuousLinearMap.adjoint (basis i)=lp.single 2 (⟨i,hi⟩ : PositiveIndex q) 1 := by
      ext j
      rw [inclusion_adjoint_coordinate]
      by_cases hji : j.val=i
      · have hjj : j=(⟨i,hi⟩ : PositiveIndex q) := Subtype.ext hji
        subst j
        simp [basis,lp.single_apply]
      · have hn : j≠(⟨i,hi⟩ : PositiveIndex q) := fun h => hji (congrArg Subtype.val h)
        simp [basis,lp.single_apply,Pi.single_apply,hji,Ne.symm hji,hn,Ne.symm hn]
    change bobIsometry v hv q u hu he ((inclusion q).toContinuousLinearMap.adjoint (basis i))=_
    rw [hj,bobIsometry_single,one_smul]
  · have hj : (inclusion q).toContinuousLinearMap.adjoint (basis i)=0 := by
      ext j
      rw [inclusion_adjoint_coordinate]
      have hn : j.val≠i := fun h => hi (h ▸ j.property)
      simp [basis,lp.single_apply,Ne.symm hn]
    change bobIsometry v hv q u hu he ((inclusion q).toContinuousLinearMap.adjoint (basis i))=_
    rw [hj,map_zero]
    simp [bobVector,Real.sqrt_eq_zero_of_nonpos (not_lt.mp hi)]

theorem bobMap_norm (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) :
    ‖bobMap v hv q u hu he‖≤1 := by
  have hJ : ‖(inclusion q).toContinuousLinearMap‖≤1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun w => by simp)
  have hJa : ‖(inclusion q).toContinuousLinearMap.adjoint‖≤1 := by simpa using hJ
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro w
  change ‖bobIsometry v hv q u hu he ((inclusion q).toContinuousLinearMap.adjoint w)‖≤1*‖w‖
  rw [LinearIsometry.norm_map,one_mul]
  exact (ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [norm_nonneg w])

/-- The Bob map is isometric precisely on the positive Schmidt coordinates. -/
theorem bobMap_gram (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) (i j : ℕ) :
    entry (star (bobMap v hv q u hu he)*bobMap v hv q u hu he) i j=
      if i=j ∧ 0<q i then 1 else 0 := by
  let V := bobMap v hv q u hu he
  have hh := ContinuousLinearMap.adjoint_inner_right V (basis i) (V (basis j))
  have hentry : entry (star V*V) i j=inner ℂ (V (basis i)) (V (basis j)) := by
    change V.adjoint (V (basis j)) i=inner ℂ (V (basis i)) (V (basis j))
    simpa only [basis,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using hh
  rw [hentry,bobMap_basis,bobMap_basis]
  by_cases hi : 0<q i
  · by_cases hj : 0<q j
    · have ho := orthonormal_iff_ite.mp (bobVector_orthonormal v hv q u hu he)
        (⟨i,hi⟩ : PositiveIndex q) (⟨j,hj⟩ : PositiveIndex q)
      simpa only [Subtype.mk.injEq,hi,and_true] using ho
    · simp [bobVector,Real.sqrt_eq_zero_of_nonpos (not_lt.mp hj),hi]
      intro hij
      subst j
      exact (hj hi).elim
  · simp [bobVector,Real.sqrt_eq_zero_of_nonpos (not_lt.mp hi),hi]

end Sigma2.UpperSchmidtMap





