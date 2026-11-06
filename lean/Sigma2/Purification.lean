import Sigma2.TensorLifts
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.Purification
open Coefficients TensorLifts

/-- Reindexing all coordinates is a Hilbert-space unitary. -/
def reindex {ι κ : Type} (e : ι ≃ κ) : Space κ ≃ₗᵢ[ℂ] Space ι where
  toFun := restrict e.toEmbedding
  invFun := restrict e.symm.toEmbedding
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  map_add' v w := by ext i; rfl
  map_smul' c v := by ext i; rfl
  norm_map' v := by
    have hh := e.tsum_eq (fun i => ‖v i‖^2)
    have hm := (norm_sq_hasSum (restrict e.toEmbedding v)).tsum_eq
    change (∑' i, ‖v (e i)‖^2)=‖restrict e.toEmbedding v‖^2 at hm
    rw [hh,(norm_sq_hasSum v).tsum_eq] at hm
    change ‖restrict e.toEmbedding v‖=‖v‖
    nlinarith [norm_nonneg (restrict e.toEmbedding v),norm_nonneg v]

@[simp] theorem reindex_apply {ι κ : Type} (e : ι ≃ κ) (v : Space κ) (i : ι) :
    reindex e v i=v (e i) := rfl

def decode : H ≃ₗᵢ[ℂ] AB := reindex Nat.pairEquiv

def amplify (A : Op) : Op := (decode.symm : AB →L[ℂ] H).comp
  ((right A).comp (decode : H →L[ℂ] AB))

@[simp] theorem decode_apply (v : H) (k i : ℕ) :
    decode v (k,i)=v (Nat.pair k i) := rfl

@[simp] theorem amplify_apply (A : Op) (v : H) (k i : ℕ) :
    amplify A v (Nat.pair k i)=A (row (decode v) k) i := by
  change right A (decode v) (Nat.unpair (Nat.pair k i))=_
  rw [Nat.unpair_pair,right_apply]

theorem amplify_positive (A : Op) (hA : A.IsPositive) : (amplify A).IsPositive := by
  have hh := (right_positive A hA).conj_adjoint (decode.symm : AB →L[ℂ] H)
  simpa only [LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm,amplify,ContinuousLinearMap.comp_assoc] using hh

@[simp] theorem amplify_one : amplify 1=1 := by
  apply ContinuousLinearMap.ext
  intro v
  ext n
  obtain ⟨⟨k,i⟩,rfl⟩ := Nat.pairEquiv.surjective n
  change amplify 1 v (Nat.pair k i)=v (Nat.pair k i)
  rw [amplify_apply]
  rfl

theorem amplify_sum {ι : Type} (t : Finset ι) (A : ι → Op) :
    amplify (∑ k ∈ t,A k)=∑ k ∈ t,amplify (A k) := by
  apply ContinuousLinearMap.ext
  intro v
  ext n
  obtain ⟨⟨k,i⟩,rfl⟩ := Nat.pairEquiv.surjective n
  change amplify (∑ c ∈ t,A c) v (Nat.pair k i)=
    ((∑ c ∈ t,amplify (A c) : Op) v) (Nat.pair k i)
  simp only [lp.coeFn_sum,Finset.sum_apply,amplify_apply,sum_apply]

/-- The environment index is paired with Alice's local coordinate. -/
def packing : ℕ × (ℕ × ℕ) ≃ ℕ × ℕ :=
  (Equiv.prodAssoc ℕ ℕ ℕ).symm.trans (Nat.pairEquiv.prodCongr (Equiv.refl ℕ))

@[simp] theorem packing_apply (k i j : ℕ) :
    packing (k,(i,j))=(Nat.pair k i,j) := rfl

@[simp] theorem packing_apply' (t : ℕ × (ℕ × ℕ)) :
    packing t=(Nat.pair t.1 t.2.1,t.2.2) := rfl

def slice (v : AB) (k : ℕ) : AB :=
  restrict ⟨fun ij => (Nat.pair k ij.1,ij.2), by
    intro ⟨i,j⟩ ⟨i',j'⟩ h
    have hh := Prod.mk.inj h
    have hi := Nat.pair_eq_pair.mp hh.1
    exact Prod.ext hi.2 hh.2⟩ v

@[simp] theorem slice_apply (v : AB) (k i j : ℕ) :
    slice v k (i,j)=v (Nat.pair k i,j) := rfl

@[simp] theorem slice_apply' (v : AB) (k : ℕ) (ij : ℕ × ℕ) :
    slice v k ij=v (Nat.pair k ij.1,ij.2) := rfl

theorem family_mass_summable (u : ℕ → AB) (hu : Summable (fun k => ‖u k‖^2)) :
    Summable (fun kij : ℕ × (ℕ × ℕ) => ‖u kij.1 kij.2‖^2) := by
  apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
  exact ⟨fun k => (norm_sq_hasSum (u k)).summable, by
    simpa only [(norm_sq_hasSum _).tsum_eq] using hu⟩

/-- Square-summable orthogonal environment components form a completed-space vector. -/
def pack (u : ℕ → AB) (hu : Summable (fun k => ‖u k‖^2)) : AB :=
  ⟨fun ij => u (packing.symm ij).1 (packing.symm ij).2,
    memℓp_gen (by
      simpa [Function.comp_def] using
        (family_mass_summable u hu).comp_injective packing.symm.injective)⟩

@[simp] theorem pack_apply (u : ℕ → AB) (hu) (k i j : ℕ) :
    pack u hu (Nat.pair k i,j)=u k (i,j) := by
  change u (packing.symm (packing (k,(i,j)))).1
    (packing.symm (packing (k,(i,j)))).2=_
  simp only [Equiv.symm_apply_apply]

@[simp] theorem pack_packing (u : ℕ → AB) (hu) (t : ℕ × (ℕ × ℕ)) :
    pack u hu (packing t)=u t.1 t.2 := by
  change u (packing.symm (packing t)).1 (packing.symm (packing t)).2=_
  simp only [Equiv.symm_apply_apply]

@[simp] theorem slice_pack (u : ℕ → AB) (hu) (k : ℕ) : slice (pack u hu) k=u k := by
  ext ⟨i,j⟩
  exact pack_apply u hu k i j

theorem pack_norm_sq (u : ℕ → AB) (hu) : ‖pack u hu‖^2=∑' k,‖u k‖^2 := by
  rw [← (norm_sq_hasSum (pack u hu)).tsum_eq,← packing.tsum_eq]
  simp only [pack_packing]
  rw [(family_mass_summable u hu).tsum_prod]
  simp only [(norm_sq_hasSum _).tsum_eq]

theorem inner_slices_summable (v w : AB) :
    Summable (fun k => inner ℂ (slice v k) (slice w k)) := by
  have hs := (lp.summable_inner (𝕜 := ℂ) v w).comp_injective packing.injective
  have hh := hs.prod
  simpa only [lp.inner_eq_tsum,Function.comp_def,packing_apply',slice_apply'] using hh

theorem inner_slices (v w : AB) :
    inner ℂ v w=∑' k,inner ℂ (slice v k) (slice w k) := by
  rw [lp.inner_eq_tsum,← packing.tsum_eq]
  have hs : Summable (fun t : ℕ × (ℕ × ℕ) =>
      inner ℂ (v (packing t)) (w (packing t))) :=
    (lp.summable_inner (𝕜 := ℂ) v w).comp_injective packing.injective
  rw [hs.tsum_prod]
  rfl

theorem slice_left (A : Op) (v : AB) (k : ℕ) :
    slice (left (amplify A) v) k=left A (slice v k) := by
  ext ⟨i,j⟩
  simp only [slice_apply,left_apply,amplify_apply]
  rfl

theorem slice_right (B : Op) (v : AB) (k : ℕ) :
    slice (right B v) k=right B (slice v k) := by
  ext ⟨i,j⟩
  simp only [slice_apply,right_apply]
  rfl

def measurements {s} (M : Measurements s) : Measurements s :=
  TensorLifts.measurements s (fun x a => amplify (M.alice x a)) M.bob
    (fun x a => amplify_positive _ (M.alice_pos x a)) M.bob_pos
    (fun x => by rw [← amplify_sum,M.alice_sum,amplify_one]) M.bob_sum

theorem slice_joint {s} (M : Measurements s) (v : AB) (k x y a b) :
    slice (((measurements M).left x a*(measurements M).right y b) v) k=
      (M.left x a*M.right y b) (slice v k) := by
  change slice (left (amplify (M.alice x a)) (right (M.bob y b) v)) k=_
  rw [slice_left,slice_right,measurements_left,measurements_right]
  rfl

theorem weighted_expectation (r : ℝ) (hr : 0≤r) (v : AB) (A : BipOp) :
    inner ℂ ((Real.sqrt r:ℂ) • v) (A ((Real.sqrt r:ℂ) • v))=
      (r:ℂ)*inner ℂ v (A v) := by
  rw [map_smul,inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  have hh : (Real.sqrt r:ℂ)*(Real.sqrt r:ℂ)=(r:ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hr
  calc
    _ = ((Real.sqrt r:ℂ)*(Real.sqrt r:ℂ))*inner ℂ v (A v) := by ring
    _ = _ := by rw [hh]

theorem pack_bob_entries {s} (S : NormalStrategy s)
    (u : ℕ → AB) (hu : Summable (fun k => ‖u k‖^2))
    (he : ∀ k,u k=(Real.sqrt (S.weight k):ℂ) • S.vector k) (i j : ℕ) :
    (∑' a,pack u hu (a,i)*star (pack u hu (a,j)))=
      ∑' k,(S.weight k:ℂ)*∑' a,S.vector k (a,i)*star (S.vector k (a,j)) := by
  let rows : ℕ × ℕ → H := fun ka => row (u ka.1) ka.2
  have hr : Summable (fun ka => ‖rows ka‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    exact ⟨fun k => (row_mass (u k)).1, by
      simpa only [rows,(row_mass _).2] using hu⟩
  have hc := coefficient_summable rows hr i j
  calc
    _ = ∑' ka : ℕ × ℕ,pack u hu (Nat.pair ka.1 ka.2,i)*
        star (pack u hu (Nat.pair ka.1 ka.2,j)) :=
      (Nat.pairEquiv.tsum_eq (fun a => pack u hu (a,i)*star (pack u hu (a,j)))).symm
    _ = ∑' ka : ℕ × ℕ,u ka.1 (ka.2,i)*star (u ka.1 (ka.2,j)) := by
      apply tsum_congr
      intro ⟨k,a⟩
      simp only [pack_apply]
    _ = ∑' k,∑' a,u k (a,i)*star (u k (a,j)) := hc.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro k
      simp_rw [he,weighted_entry _ (S.weight_nonneg k),tsum_mul_left]

theorem marginalB_pure {s} (T : PureStrategy s) (h : Density) :
    MarginalB (normalOfPure T) h ↔ ∀ i j,
      entry h.op i j=∑' a,T.vector (a,i)*star (T.vector (a,j)) := by
  simp only [MarginalB,normalOfPure]
  have he (k : ℕ) : ((if k=0 then 1 else 0 : ℝ):ℂ)=if k=0 then 1 else 0 := by
    split_ifs <;> rfl
  simp [he,ite_mul]

theorem exists_pure_preserving_bob {s} (S : NormalStrategy s) :
    ∃ T : PureStrategy s,
      T.measurements=measurements S.measurements ∧
      (∀ h : Density,MarginalB S h → MarginalB (normalOfPure T) h) ∧
      (∀ x y a b,S.probability x y a b=T.probability x y a b) := by
  let u : ℕ → AB := fun k => (Real.sqrt (S.weight k):ℂ) • S.vector k
  have hnorm k : ‖u k‖^2=S.weight k :=
    weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k)
  have hu : Summable (fun k => ‖u k‖^2) := by
    simpa only [hnorm] using S.weight_summable
  let Ω := pack u hu
  have hΩ : ‖Ω‖=1 := by
    have hh := pack_norm_sq u hu
    simp only [hnorm,S.weight_sum] at hh
    change ‖Ω‖^2=1 at hh
    nlinarith [norm_nonneg Ω]
  let T : PureStrategy s := ⟨measurements S.measurements,Ω,hΩ⟩
  refine ⟨T,rfl,?_,?_⟩
  · intro h hm
    apply (marginalB_pure T h).mpr
    intro i j
    exact (hm i j).trans (pack_bob_entries S u hu (fun _ => rfl) i j).symm
  intro x y a b
  change _=(inner ℂ Ω (((measurements S.measurements).left x a*
    (measurements S.measurements).right y b) Ω)).re
  rw [inner_slices]
  have hs := inner_slices_summable Ω
    (((measurements S.measurements).left x a*(measurements S.measurements).right y b) Ω)
  change _=Complex.reCLM (∑' k,inner ℂ (slice Ω k)
    (slice (((measurements S.measurements).left x a*
      (measurements S.measurements).right y b) Ω) k))
  rw [Complex.reCLM.map_tsum hs]
  apply tsum_congr
  intro k
  rw [slice_joint]
  dsimp only [Ω]
  rw [slice_pack]
  change S.weight k*(S.component k).probability x y a b=
    (inner ℂ (u k) ((S.measurements.left x a*S.measurements.right y b) (u k))).re
  rw [weighted_expectation _ (S.weight_nonneg k)]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rfl

theorem exists_pure {s} (S : NormalStrategy s) :
    ∃ T : PureStrategy s, ∀ x y a b,S.probability x y a b=T.probability x y a b := by
  obtain ⟨T,_,_,hT⟩ := exists_pure_preserving_bob S
  exact ⟨T,hT⟩

#print axioms exists_pure_preserving_bob
#print axioms exists_pure
end Sigma2.Purification
