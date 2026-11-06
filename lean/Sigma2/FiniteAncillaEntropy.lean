import Sigma2.FiniteAncillaDensity

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.FiniteAncilla
open Coefficients FiniteSum TensorLifts
variable (d : ℕ) [NeZero d]

theorem repeat_summable (f : ℕ → ℝ) (hf : Summable f) : Summable (fun p : Fin d × ℕ => f p.2) := by
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun p => norm_nonneg (f p.2))).mpr
  exact ⟨fun a => hf.norm,(hasSum_fintype _).summable⟩

theorem entropyTerm_div (p : ℝ) (hp : 0≤p) :
    entropyTerm (p/(d:ℝ))=entropyTerm p/(d:ℝ)+
      (p/(d:ℝ))*(Real.log (d:ℝ)/Real.log 2) := by
  by_cases hpz : p=0
  · simp [hpz,entropyTerm]
  have hd : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
  have hlog : Real.log (2:ℝ)≠0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold entropyTerm
  rw [Real.log_div hpz hd]
  field_simp
  <;> ring

/-- Each old eigenvalue p becomes d copies of p/d. -/
def eigenvalue (p : ℕ → ℝ) (n : ℕ) : ℝ := p ((coordinates d).symm n).2/(d:ℝ)

theorem eigenvalue_summable (p : ℕ → ℝ) (hp : Summable p) :
    Summable (eigenvalue d p) := by
  apply (coordinates d).summable_iff.mp
  simpa only [Function.comp_def,eigenvalue,Equiv.symm_apply_apply] using
    repeat_summable d (fun i => p i/(d:ℝ)) (hp.div_const _)

theorem eigenvalue_sum (p : ℕ → ℝ) (hp : Summable p) :
    (∑' n,eigenvalue d p n)=∑' n,p n := by
  rw [← (coordinates d).tsum_eq]
  simp only [eigenvalue,Equiv.symm_apply_apply]
  rw [(repeat_summable d (fun i => p i/(d:ℝ)) (hp.div_const _)).tsum_prod,
    tsum_fintype]
  have hd : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
  simp only [tsum_div_const,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

theorem eigenvalue_entropy_summable (p : ℕ → ℝ) (hp0 : ∀ i,0≤p i)
    (hp : Summable p) (hh : Summable (fun i => entropyTerm (p i))) :
    Summable (fun n => entropyTerm (eigenvalue d p n)) := by
  apply (coordinates d).summable_iff.mp
  have hs : Summable (fun i => entropyTerm (p i/(d:ℝ))) := by
    simp_rw [entropyTerm_div d _ (hp0 _)]
    exact (hh.div_const _).add ((hp.div_const _).mul_right _)
  simpa only [Function.comp_def,eigenvalue,Equiv.symm_apply_apply] using
    repeat_summable d _ hs

/-- The spectral entropy increases by exactly log2(d). -/
theorem eigenvalue_entropy_sum (p : ℕ → ℝ) (hp0 : ∀ i,0≤p i)
    (hp : Summable p) (hp1 : (∑' i,p i)=1)
    (hh : Summable (fun i => entropyTerm (p i))) :
    (∑' n,entropyTerm (eigenvalue d p n))=
      (∑' n,entropyTerm (p n))+Real.log (d:ℝ)/Real.log 2 := by
  rw [← (coordinates d).tsum_eq]
  simp only [eigenvalue,Equiv.symm_apply_apply]
  have hs : Summable (fun i => entropyTerm (p i/(d:ℝ))) := by
    simp_rw [entropyTerm_div d _ (hp0 _)]
    exact (hh.div_const _).add ((hp.div_const _).mul_right _)
  rw [(repeat_summable d _ hs).tsum_prod,tsum_fintype]
  simp_rw [entropyTerm_div d _ (hp0 _)]
  rw [Summable.tsum_add (hh.div_const _) ((hp.div_const _).mul_right _)]
  simp only [tsum_div_const,tsum_mul_right,hp1,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  have hd : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
  field_simp
  <;> ring

def eigenvector (u : ℕ → H) (n : ℕ) : H :=
  FiniteSum.insert (coordinates d) ((coordinates d).symm n).1 (u ((coordinates d).symm n).2)

theorem insert_inner (a : Fin d) (v : H) (w : H) :
    inner ℂ (FiniteSum.insert (coordinates d) a v) w=inner ℂ v (fiber (coordinates d) w a) := by
  have hh := ContinuousLinearMap.adjoint_inner_right
    (FiniteSum.insert (coordinates d) a).toContinuousLinearMap v w
  simpa only [FiniteSum.insert_adjoint,project_apply,LinearIsometry.coe_toContinuousLinearMap]
    using hh.symm

theorem eigenvector_orthonormal (u : ℕ → H) (hu : Orthonormal ℂ u) :
    Orthonormal ℂ (eigenvector d u) := by
  rw [orthonormal_iff_ite]
  intro i j
  obtain ⟨⟨a,i⟩,rfl⟩ := (coordinates d).surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := (coordinates d).surjective j
  simp only [eigenvector,Equiv.symm_apply_apply,insert_inner,fiber_insert]
  have he : coordinates d (a,i)=coordinates d (b,j) ↔ a=b ∧ i=j := by
    rw [Equiv.apply_eq_iff_eq,Prod.mk.injEq]
  simp only [he]
  by_cases hab : a=b
  · subst b
    simp only [ite_true,true_and,orthonormal_iff_ite.mp hu]
  · simp only [if_neg (Ne.symm hab),inner_zero_right,hab,false_and,ite_false]

theorem spectral_series_summable (p : ℕ → ℝ) (u : ℕ → H)
    (hp0 : ∀ i,0≤p i) (hp : Summable p) (hu : Orthonormal ℂ u) (v : H) :
    Summable (fun i => ((p i:ℂ)*inner ℂ (u i) v) • u i) := by
  apply Summable.of_norm_bounded (hp.mul_right ‖v‖)
  intro i
  rw [norm_smul,norm_mul,hu.norm_eq_one,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (hp0 i)]
  apply mul_le_mul_of_nonneg_left _ (hp0 i)
  simpa only [hu.norm_eq_one,one_mul] using norm_inner_le_norm (u i) v

/-- An exact eigen-expansion of the normalized finite tensor density. -/
theorem density_spectral (h : Density) (p : ℕ → ℝ) (u : ℕ → H)
    (hp0 : ∀ i,0≤p i) (hp : Summable p) (hu : Orthonormal ℂ u)
    (he : ∀ v,h.op v=∑' i,((p i:ℂ)*inner ℂ (u i) v) • u i) (v : H) :
    (density d h).op v=
      ∑' n,((eigenvalue d p n:ℂ)*inner ℂ (eigenvector d u n) v) • eigenvector d u n := by
  have hp' : ∀ n,0≤eigenvalue d p n := fun n => div_nonneg (hp0 _) (Nat.cast_nonneg _)
  have hs := spectral_series_summable (eigenvalue d p) (eigenvector d u) hp'
    (eigenvalue_summable d p hp) (eigenvector_orthonormal d u hu) v
  apply ext_fiber (coordinates d)
  intro a
  change fiber (coordinates d) ((1/(d:ℂ)) • amplify d h.op v) a=
    project (coordinates d) a (∑' n,
      ((eigenvalue d p n:ℂ)*inner ℂ (eigenvector d u n) v) • eigenvector d u n)
  rw [(project (coordinates d) a).map_tsum hs]
  rw [← (coordinates d).tsum_eq]
  have hsprod := ((hs.hasSum.mapL (project (coordinates d) a)).summable).comp_injective
    (coordinates d).injective
  dsimp only [Function.comp_def] at hsprod
  rw [hsprod.tsum_prod,tsum_fintype]
  simp only [eigenvalue,eigenvector,Equiv.symm_apply_apply,map_smul,project_apply,
    fiber_insert,insert_inner]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true,fiber_smul,fiber_amplify,he]
    rw [← (spectral_series_summable p u hp0 hp hu (fiber (coordinates d) v a)).tsum_const_smul (1/(d:ℂ))]
    apply tsum_congr
    intro i
    push_cast
    rw [smul_smul]
    congr 1
    ring
  · intro b hb hba
    simp only [if_neg (Ne.symm hba),smul_zero,tsum_zero]
  · simp

theorem finiteDensityEntropy (h : Density) (hh : FiniteDensityEntropy h) :
    FiniteDensityEntropy (density d h) := by
  obtain ⟨p,u,hp0,hp,hp1,hu,he,hent⟩ := hh
  exact ⟨eigenvalue d p,eigenvector d u,
    fun n => div_nonneg (hp0 _) (Nat.cast_nonneg _),
    eigenvalue_summable d p hp,(eigenvalue_sum d p hp).trans hp1,
    eigenvector_orthonormal d u hu,density_spectral d h p u hp0 hp hu he,
    eigenvalue_entropy_summable d p hp0 hp hent⟩

/-- Both original finite spectral marginal entropies survive the same ancilla. -/
theorem finiteMarginalEntropy {s} (S : NormalStrategy s) (hh : FiniteMarginalEntropy S) :
    FiniteMarginalEntropy (strategy d S) := by
  obtain ⟨hA,hB,hmA,hmB,hhA,hhB⟩ := hh
  exact ⟨density d hA,density d hB,marginalA d S hA hmA,marginalB d S hB hmB,
    finiteDensityEntropy d hA hhA,finiteDensityEntropy d hB hhB⟩

end Sigma2.FiniteAncilla
