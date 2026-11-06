import Sigma2.NormalCoefficients
import Mathlib.Basic.Denumerable

/-! Bounded diagonal and injection-shift operators on countable Hilbert sums.
The index set is arbitrary; there are no presentation or automaton parameters. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
namespace Sigma2.FockModel
open Coefficients
variable {ι κ : Type}

abbrev Space (ι : Type) := lp (fun _ : ι => ℂ) 2
abbrev Operator (ι : Type) := Space ι →L[ℂ] Space ι

/-- An explicit change of coordinate names, preserving the Hilbert norm. -/
def reindex (e : ι ≃ κ) : Space κ ≃ₗᵢ[ℂ] Space ι where
  toFun := restrict e.toEmbedding
  invFun := restrict e.symm.toEmbedding
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  map_add' v w := by ext i; rfl
  map_smul' c v := by ext i; rfl
  norm_map' v := by
    have ht := e.tsum_eq (fun i => ‖v i‖^2)
    have hn := (norm_sq_hasSum (restrict e.toEmbedding v)).tsum_eq
    change (∑' i, ‖v (e i)‖^2)=_ at hn
    rw [ht, (norm_sq_hasSum v).tsum_eq] at hn
    change ‖restrict e.toEmbedding v‖=‖v‖
    nlinarith [norm_nonneg (restrict e.toEmbedding v),norm_nonneg v]

@[simp] theorem reindex_apply (e : ι ≃ κ) (v : Space κ) (i : ι) :
    reindex e v i = v (e i) := rfl

/-- Enumeration realizes an indexed Hilbert basis in the fixed ambient space. -/
def basis (e : ι ≃ ℕ) : HilbertBasis ι ℂ H := HilbertBasis.ofRepr (reindex e)

@[simp] theorem basis_eq (e : ι ≃ ℕ) (i : ι) :
    basis e i = Sigma2.basis (e i) := by
  classical
  ext n
  change (lp.single 2 i (1:ℂ) : Space ι) (e.symm n) = (lp.single 2 (e i) (1:ℂ) : H) n
  simp only [lp.single_apply,Pi.single_apply]
  by_cases h : n=e i
  · subst n; simp
  · have hh : e.symm n ≠ i := fun hh => h (by simpa using congrArg e hh)
    simp [h,hh]

abbrev Bounded (c : ι → ℂ) : Prop := ∃ M : ℝ, ∀ i, ‖c i‖≤M

lemma bounded_const (z : ℂ) : Bounded (fun _ : ι => z) := ⟨‖z‖,fun _ => le_rfl⟩
lemma bounded_mul {c d : ι → ℂ} (hc : Bounded c) (hd : Bounded d) :
    Bounded (fun i => c i*d i) := by
  obtain ⟨M,hM⟩ := hc
  obtain ⟨N,hN⟩ := hd
  refine ⟨|M| * |N|,?_⟩
  intro i
  rw [norm_mul]
  exact mul_le_mul ((hM i).trans (le_abs_self _))
    ((hN i).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)
lemma bounded_star {c : ι → ℂ} (hc : Bounded c) : Bounded (fun i => star (c i)) := by
  obtain ⟨M,hM⟩ := hc
  exact ⟨M,fun i => by simpa using hM i⟩

def diagonalVector (c : ι → ℂ) (hc : Bounded c) (v : Space ι) : Space ι :=
  ⟨fun i => c i*v i, ((lp.memℓp v).norm.const_smul |hc.choose|).mono (fun i => by
    change ‖c i*v i‖≤ |hc.choose| *‖v i‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((hc.choose_spec i).trans (le_abs_self _)) (norm_nonneg _))⟩

lemma diagonalVector_bound (c : ι → ℂ) (hc : Bounded c) (v : Space ι)
    (M : ℝ) (hM : 0≤M) (h : ∀ i, ‖c i‖≤M) :
    ‖diagonalVector c hc v‖≤M*‖v‖ := by
  let vn : lp (fun _ : ι => ℝ) 2 := ⟨fun i => ‖v i‖,(lp.memℓp v).norm⟩
  have hh : ‖diagonalVector c hc v‖≤‖M • vn‖ := by
    apply lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0)
    intro i
    change ‖c i*v i‖≤‖M*‖v i‖‖
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg hM (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (h i) (norm_nonneg _)
  have hn : ‖vn‖=‖v‖ := by
    apply le_antisymm <;> apply lp.norm_mono (by norm_num : (2:ℝ≥0∞)≠0) <;>
      intro i <;> simp [vn]
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hM,hn] using hh

/-- Multiplication by any uniformly bounded family of complex coefficients. -/
def diagonal (c : ι → ℂ) (hc : Bounded c) : Operator ι :=
  LinearMap.mkContinuous
    { toFun := diagonalVector c hc
      map_add' := by intros; ext i; exact mul_add _ _ _
      map_smul' := by intros; ext i; simp only [diagonalVector,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]; ring }
    |hc.choose| (fun v => diagonalVector_bound c hc v _ (abs_nonneg _)
      (fun i => (hc.choose_spec i).trans (le_abs_self _)))

@[simp] theorem diagonal_apply (c : ι → ℂ) (hc) (v : Space ι) (i : ι) :
    diagonal c hc v i=c i*v i := rfl

lemma diagonal_norm_le (c : ι → ℂ) (hc) (M : ℝ) (hM : 0≤M)
    (h : ∀ i, ‖c i‖≤M) : ‖diagonal c hc‖≤M :=
  ContinuousLinearMap.opNorm_le_bound _ hM (fun v => diagonalVector_bound c hc v M hM h)

lemma diagonal_mul (c d : ι → ℂ) (hc) (hd) :
    diagonal c hc*diagonal d hd=diagonal (fun i => c i*d i) (bounded_mul hc hd) := by
  ext v i
  simp only [mul_apply_eq_comp,diagonal_apply]
  ring

lemma diagonal_const (z : ℂ) :
    diagonal (fun _ : ι => z) (bounded_const z)=z • (1 : Operator ι) := by
  ext v i; rfl

lemma diagonal_star (c : ι → ℂ) (hc) :
    star (diagonal c hc)=diagonal (fun i => star (c i)) (bounded_star hc) := by
  symm
  change _ = ContinuousLinearMap.adjoint _
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  simp only [lp.inner_eq_tsum,diagonal_apply,RCLike.inner_apply]
  apply tsum_congr
  intro i
  simp [map_mul,mul_comm,mul_left_comm,mul_assoc]

lemma diagonal_single (c : ι → ℂ) (hc) (i : ι) :
    diagonal c hc (lp.single 2 i 1)=c i • lp.single 2 i 1 := by
  classical
  ext j
  by_cases h : i=j
  · subst j; simp
  · simp [lp.single_apply,Pi.single_apply,h]

/-- Operators agree once they agree on the coordinate unit vectors. -/
theorem ext_basis (A B : Operator ι)
    (h : ∀ i, A (lp.single 2 i 1)=B (lp.single 2 i 1)) : A=B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞)≠⊤)
  intro i
  apply ContinuousLinearMap.ext
  intro c
  change A (lp.single 2 i c)=B (lp.single 2 i c)
  have he : (lp.single 2 i c : Space ι)=c • lp.single 2 i 1 := by
    simp only [← lp.single_smul,smul_eq_mul,mul_one]
  rw [he,map_smul,map_smul,h]

lemma diagonal_positive (p : ι → ℝ) (hp : ∀ i, 0≤p i)
    (hb : Bounded (fun i => (p i : ℂ))) :
    (diagonal (fun i => (p i : ℂ)) hb).IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr ⟨?_,?_⟩
  · change star (diagonal (fun i => (p i : ℂ)) hb)=_
    rw [diagonal_star]
    congr 1
    funext i
    exact Complex.conj_ofReal _
  · intro v
    change 0≤(inner ℂ (diagonal (fun i => (p i : ℂ)) hb v) v).re
    have hh := (lp.hasSum_inner (diagonal (fun i => (p i : ℂ)) hb v) v).mapL Complex.reCLM
    change HasSum (fun i => (inner ℂ (diagonal (fun i => (p i : ℂ)) hb v i) (v i)).re)
      (inner ℂ (diagonal (fun i => (p i : ℂ)) hb v) v).re at hh
    rw [← hh.tsum_eq]
    apply tsum_nonneg
    intro i
    change 0≤(inner ℂ ((p i : ℂ)*v i) (v i)).re
    rw [show (p i : ℂ)*v i=(p i : ℂ) • v i from rfl,inner_smul_left,
      Complex.conj_ofReal,inner_self_eq_norm_sq_to_K,Complex.mul_re]
    simpa [pow_two,Complex.mul_re,Complex.mul_im] using mul_nonneg (hp i) (sq_nonneg ‖v i‖)

/-- Indicator diagonals are orthogonal projections. -/
def projection (s : Set ι) : Operator ι :=
  diagonal (fun i => if i∈s then 1 else 0) ⟨1,fun i => by dsimp; split_ifs <;> norm_num⟩

lemma projection_spec (s : Set ι) :
    star (projection s)=projection s ∧ projection s*projection s=projection s := by
  constructor
  · rw [projection,diagonal_star]
    congr 1
    funext i
    split_ifs <;> simp
  · ext v i
    change (if i∈s then (1:ℂ) else 0)*((if i∈s then (1:ℂ) else 0)*v i)=
      (if i∈s then (1:ℂ) else 0)*v i
    split_ifs <;> simp

@[simp] lemma projection_single (s : Set ι) (i : ι) :
    projection s (lp.single 2 i 1)=if i∈s then lp.single 2 i 1 else 0 := by
  rw [projection,diagonal_single]
  split_ifs <;> simp

/-- Every injective coordinate map gives an isometry, extended by zero. -/
def shift (f : ι ↪ κ) : Space ι →L[ℂ] Space κ := (embed f).toContinuousLinearMap

@[simp] lemma shift_single (f : ι ↪ κ) (i : ι) :
    shift f (lp.single 2 i 1)=lp.single 2 (f i) 1 := by
  simp [shift,embed,OrthogonalFamily.linearIsometry_apply_single,
    Orthonormal.orthogonalFamily,LinearIsometry.toSpanSingleton_apply,
    HilbertBasis.ofRepr]
  rfl

lemma shift_isometry (f : ι ↪ κ) :
    (shift f).adjoint.comp (shift f)=1 := (embed f).adjoint_comp_self

@[simp] lemma adjoint_shift_apply (f : ι ↪ κ) (v : Space κ) (i : ι) :
    (shift f).adjoint v i=v (f i) := by
  have hh := ContinuousLinearMap.adjoint_inner_right (shift f) (lp.single 2 i 1) v
  simpa only [shift_single,lp.inner_single_left,RCLike.inner_apply,
    map_one,mul_one] using hh

lemma shift_apply_at (f : ι ↪ κ) (v : Space ι) (i : ι) :
    shift f v (f i)=v i := by
  have hh := congrArg (fun A : Operator ι => A v i) (shift_isometry f)
  simpa using hh

lemma shift_apply_off (f : ι ↪ κ) (v : Space ι) (j : κ) (hj : j∉Set.range f) :
    shift f v j=0 := by
  have hh := ((lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) v).mapL
    (shift f)).mapL (lp.evalCLM ℂ (fun _ : κ => ℂ) 2 j)
  have he (i : ι) : (lp.single 2 i (v i) : Space ι)=v i • lp.single 2 i 1 := by
    simp only [← lp.single_smul,smul_eq_mul,mul_one]
  have hz (i : ι) : (lp.single 2 (f i) 1 : Space κ) j=0 := by
    simp [lp.single_apply,show f i≠j from fun h => hj ⟨i,h⟩]
  have hs : HasSum (fun _ : ι => (0 : ℂ)) (shift f v j) := by
    simp only [he,map_smul,shift_single] at hh
    change HasSum (fun i => v i*(lp.single 2 (f i) 1 : Space κ) j) (shift f v j) at hh
    simpa only [hz,mul_zero] using hh
  exact hs.unique hasSum_zero

lemma shift_range (f : ι ↪ κ) :
    (shift f).comp (shift f).adjoint=projection (Set.range f) := by
  ext v j
  by_cases hj : j∈Set.range f
  · obtain ⟨i,rfl⟩ := hj
    simp [shift_apply_at,projection,diagonal_apply]
  · change shift f ((shift f).adjoint v) j=(if j∈Set.range f then (1:ℂ) else 0)*v j
    rw [if_neg hj,shift_apply_off f _ j hj,zero_mul]

/-- A weighted injection shift; diagonal and shift rules supply its algebra. -/
def weightedShift (f : ι ↪ κ) (c : ι → ℂ) (hc : Bounded c) :
    Space ι →L[ℂ] Space κ := (shift f).comp (diagonal c hc)

@[simp] lemma weightedShift_single (f : ι ↪ κ) (c : ι → ℂ) (hc) (i : ι) :
    weightedShift f c hc (lp.single 2 i 1)=c i • lp.single 2 (f i) 1 := by
  simp [weightedShift,diagonal_single]

#print axioms diagonal_mul
#print axioms diagonal_star
#print axioms diagonal_positive
#print axioms projection_spec
#print axioms shift_range
end Sigma2.FockModel
