import Sigma2.UpperSchmidtSpectrum

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.UpperSchmidtOperators
open UpperSchmidtSpectrum

/-- The scalar diagonal acts contractively on the fixed Hilbert model. -/
theorem coordinate_bound (d : ℕ → ℝ) (hd : ∀ i,|d i|≤1) (v : H) (i : ℕ) :
    ‖(d i:ℂ)*v i‖≤‖v i‖ := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hd i) (norm_nonneg _)).trans_eq (one_mul _)

def diagonalVector (d : ℕ → ℝ) (hd : ∀ i,|d i|≤1) (v : H) : H :=
  ⟨fun i => (d i:ℂ)*v i,(lp.memℓp v).mono' (coordinate_bound d hd v)⟩

def diagonalOp (d : ℕ → ℝ) (hd : ∀ i,|d i|≤1) : Op :=
  LinearMap.mkContinuous
    { toFun := diagonalVector d hd
      map_add' := by intro v w; ext i; exact mul_add _ _ _
      map_smul' := by intro c v; ext i; change (d i:ℂ)*(c*v i)=c*((d i:ℂ)*v i); ring }
    1 (fun v => by
      rw [one_mul]
      apply lp.norm_mono (by norm_num : (2:ENNReal)≠0)
      exact coordinate_bound d hd v)

@[simp] theorem diagonalOp_apply (d : ℕ → ℝ) (hd : ∀ i,|d i|≤1) (v : H) (i : ℕ) :
    diagonalOp d hd v i=(d i:ℂ)*v i := rfl

theorem diagonalOp_diagonal (d : ℕ → ℝ) (hd : ∀ i,|d i|≤1) :
    UpperAmplitudes.Diagonal (diagonalOp d hd) d := by
  intro i j
  change (d i:ℂ)*basis j i=if i=j then (d i:ℂ) else 0
  by_cases hij : i=j <;> simp [hij,basis,lp.single_apply]

/-- Cross pairings of contracted vectors recover the reduced density. -/
theorem fiber_pairing (v : AB) (hv : ‖v‖=1) (a b : H) :
    inner ℂ (fiber v a) (fiber v b)=inner ℂ b ((density v hv).op a) := by
  change inner ℂ (fiber v a) (fiber v b)=inner ℂ b (Coefficients.covariance (Coefficients.column v) a)
  rw [lp.inner_eq_tsum,← (Coefficients.covariance_hasSum (Coefficients.column v)
    (Coefficients.column_mass v).1 b a).tsum_eq]
  apply tsum_congr
  intro j
  simp only [fiber_apply,RCLike.inner_apply]
  rw [← inner_conj_symm a (Coefficients.column v j)]
  simp

/-- The Bob Schmidt vectors on positive spectral indices. Zero coefficients
produce zero vectors and require a complementary deterministic POVM outcome. -/
def bobVector (v : AB) (q : ℕ → ℝ) (u : ℕ → H) (i : ℕ) : H :=
  ((Real.sqrt (q i))⁻¹:ℂ) • fiber v (u i)

theorem bobVector_orthonormal (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) :
    Orthonormal ℂ (fun i : {i : ℕ // 0<q i} => bobVector v q u i) := by
  rw [orthonormal_iff_ite]
  intro i j
  simp only [bobVector,inner_smul_left,inner_smul_right,fiber_pairing v hv,
    EntropyMinMax.apply_spectral_vector (density v hv) q u hu he,inner_smul_right]
  by_cases hij : i=j
  · subst j
    have hq : Real.sqrt (q i.val)≠0 := ne_of_gt (Real.sqrt_pos.mpr i.property)
    rw [inner_self_eq_norm_sq_to_K,hu.norm_eq_one]
    simp only [one_pow,Complex.ofReal_one,mul_one,ite_true]
    have hc : (starRingEnd ℂ) ((Real.sqrt (q i.val))⁻¹:ℂ)=((Real.sqrt (q i.val))⁻¹:ℂ) := by simp
    rw [hc]
    push_cast
    field_simp
    norm_cast
    rw [Real.sq_sqrt i.property.le]
    exact div_self (ne_of_gt i.property)
  · have hji : j.val≠i.val := fun h => hij (Subtype.ext h.symm)
    rw [hu.inner_eq_zero hji]
    simp [hij]

/-- Synthesis by an orthonormal family is an isometry, even if its range is proper. -/
def synthesis (u : ℕ → H) (hu : Orthonormal ℂ u) : H →ₗᵢ[ℂ] H :=
  hu.orthogonalFamily.linearIsometry

@[simp] theorem synthesis_basis (u : ℕ → H) (hu : Orthonormal ℂ u) (i : ℕ) :
    synthesis u hu (basis i)=u i := by
  simp [synthesis,basis,OrthogonalFamily.linearIsometry_apply_single]

theorem synthesis_adjoint_coordinate (u : ℕ → H) (hu : Orthonormal ℂ u) (w : H) (i : ℕ) :
    (synthesis u hu).toContinuousLinearMap.adjoint w i=inner ℂ (u i) w := by
  have hh := ContinuousLinearMap.adjoint_inner_right (synthesis u hu).toContinuousLinearMap (basis i) w
  change inner ℂ (basis i) ((synthesis u hu).toContinuousLinearMap.adjoint w)=inner ℂ (synthesis u hu (basis i)) w at hh
  rw [synthesis_basis] at hh
  simpa only [basis,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one] using hh

/-- Every original column lies in the closed span of the nonzero reduced spectrum.
This handles a nontrivial kernel without asserting that the sorted eigenfamily is a basis. -/
theorem column_expansion (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) (j : ℕ) :
    Coefficients.column v j=∑' i,(fiber v (u i) j) • u i := by
  let U : Op := (synthesis u hu).toContinuousLinearMap
  let c : H := Coefficients.column v j
  let r : H := c-U (U.adjoint c)
  have hUU (w : H) : U.adjoint (U w)=w :=
    congrArg (fun A : Op => A w) (synthesis u hu).adjoint_comp_self
  have hUr : U.adjoint r=0 := by simp only [r,map_sub,hUU,sub_self]
  have hinner (i : ℕ) : inner ℂ (u i) r=0 := by
    rw [← synthesis_adjoint_coordinate u hu r i]
    change U.adjoint r i=0
    rw [hUr]
    rfl
  have hker : (density v hv).op r=0 := by simp [he,hinner]
  have hrc : inner ℂ r c=0 :=
    ((Coefficients.covariance_kernel (Coefficients.column v) (Coefficients.column_mass v).1 r).mp hker) j
  have hrp : inner ℂ r (U (U.adjoint c))=0 := by
    rw [← ContinuousLinearMap.adjoint_inner_left,hUr,inner_zero_left]
  have hr : r=0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    change inner ℂ r (c-U (U.adjoint c))=0
    rw [inner_sub_right,hrc,hrp,sub_self]
  have hc : c=U (U.adjoint c) := sub_eq_zero.mp hr
  rw [show Coefficients.column v j=c from rfl,hc]
  change synthesis u hu (U.adjoint c)=_
  rw [synthesis,OrthogonalFamily.linearIsometry_apply]
  apply tsum_congr
  intro i
  rw [show U.adjoint c i=inner ℂ (u i) c from synthesis_adjoint_coordinate u hu c i]
  rfl

/-- The zero-probability fiber vanishes, so inverse square roots introduce no spurious vector. -/
theorem fiber_eq_sqrt_bobVector (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hq : ∀ i,0≤q i) (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) (i : ℕ) :
    fiber v (u i)=(Real.sqrt (q i):ℂ) • bobVector v q u i := by
  by_cases hz : q i=0
  · have hn : ‖fiber v (u i)‖^2=0 := by
      rw [fiber_norm_sq v hv,EntropyMinMax.apply_spectral_vector (density v hv) q u hu he i,hz]
      simp
    have hf : fiber v (u i)=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    simp [hf,hz,bobVector]
  · have hs : (Real.sqrt (q i):ℂ)≠0 := by
      exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr (lt_of_le_of_ne (hq i) (Ne.symm hz)))
    simp only [bobVector,smul_smul,mul_inv_cancel₀ hs,one_smul]

/-- Coordinate Schmidt decomposition of the original completed tensor vector. -/
theorem schmidt_coordinates (v : AB) (hv : ‖v‖=1) (q : ℕ → ℝ) (u : ℕ → H)
    (hq : ∀ i,0≤q i) (hu : Orthonormal ℂ u)
    (he : ∀ w,(density v hv).op w=∑' i,((q i:ℂ)*inner ℂ (u i) w) • u i) (a b : ℕ) :
    v (a,b)=∑' i,(Real.sqrt (q i):ℂ)*u i a*bobVector v q u i b := by
  have hh := column_expansion v hv q u hu he b
  have hs := hu.orthogonalFamily.summable_of_lp
    ((synthesis u hu).toContinuousLinearMap.adjoint (Coefficients.column v b))
  change Summable (fun i => ((synthesis u hu).toContinuousLinearMap.adjoint (Coefficients.column v b) i) • u i) at hs
  simp_rw [synthesis_adjoint_coordinate] at hs
  have hh' : HasSum (fun i => (fiber v (u i) b) • u i) (Coefficients.column v b) := by
    rw [hh]
    exact hs.hasSum
  have ht := hh'.mapL (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 a)
  change HasSum (fun i => (fiber v (u i) b)*u i a) (v (a,b)) at ht
  rw [← ht.tsum_eq]
  apply tsum_congr
  intro i
  rw [fiber_eq_sqrt_bobVector v hv q u hq hu he i]
  change ((Real.sqrt (q i):ℂ)*bobVector v q u i b)*u i a=_
  ring
end Sigma2.UpperSchmidtOperators




