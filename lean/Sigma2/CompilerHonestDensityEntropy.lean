import Sigma2.CompilerHonestDensity
import Sigma2.FiniteAncillaEntropy

/-! Finite-entropy preservation by the honest seventeen-corner density and its
scalar qutrit factor, without replacing the frozen strategy entropy interface. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerHonestDensityEntropy
open FiniteAncilla FiniteSum
open CompilerHonestDensity
variable (d : ℕ) [NeZero d]

theorem finite_family_summable (f : Fin d → ℕ → ℝ) (hf : ∀ a,Summable (f a)) :
    Summable (fun p : Fin d × ℕ => f p.1 p.2) := by
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
  exact ⟨fun a => (hf a).norm,(hasSum_fintype _).summable⟩

theorem entropyTerm_mul (a p : ℝ) (ha : 0≤a) (hp : 0≤p) :
    entropyTerm (a*p)=a*entropyTerm p+p*entropyTerm a := by
  by_cases haz : a=0
  · simp [haz,entropyTerm]
  by_cases hpz : p=0
  · simp [hpz,entropyTerm]
  unfold entropyTerm
  rw [Real.log_mul haz hpz]
  ring

def eigenvalue (w : Fin d → ℝ) (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  w ((coordinates d).symm n).1*p ((coordinates d).symm n).2

theorem eigenvalue_summable (w : Fin d → ℝ) (p : ℕ → ℝ) (hp : Summable p) :
    Summable (eigenvalue d w p) := by
  apply (coordinates d).summable_iff.mp
  simpa only [Function.comp_def,eigenvalue,Equiv.symm_apply_apply] using
    finite_family_summable d (fun a i => w a*p i) (fun a => hp.mul_left (w a))

theorem eigenvalue_sum (w : Fin d → ℝ) (hw : ∑ a,w a=1)
    (p : ℕ → ℝ) (hp : Summable p) (hp1 : (∑' i,p i)=1) :
    (∑' n,eigenvalue d w p n)=1 := by
  rw [← (coordinates d).tsum_eq]
  simp only [eigenvalue,Equiv.symm_apply_apply]
  rw [(finite_family_summable d (fun a i => w a*p i) (fun a => hp.mul_left (w a))).tsum_prod,
    tsum_fintype]
  simpa only [tsum_mul_left,hp1,mul_one] using hw

theorem eigenvalue_entropy_summable (w : Fin d → ℝ) (hw : ∀ a,0≤w a)
    (p : ℕ → ℝ) (hp0 : ∀ i,0≤p i) (hp : Summable p)
    (hh : Summable (fun i => entropyTerm (p i))) :
    Summable (fun n => entropyTerm (eigenvalue d w p n)) := by
  apply (coordinates d).summable_iff.mp
  have hs (a : Fin d) : Summable (fun i => entropyTerm (w a*p i)) := by
    simp_rw [entropyTerm_mul _ _ (hw a) (hp0 _)]
    exact (hh.mul_left (w a)).add (hp.mul_right (entropyTerm (w a)))
  simpa only [Function.comp_def,eigenvalue,Equiv.symm_apply_apply] using
    finite_family_summable d (fun a i => entropyTerm (w a*p i)) hs

/-- The entropy increase is exactly the entropy of the finite scalar weights. -/
theorem eigenvalue_entropy_sum (w : Fin d → ℝ) (hw0 : ∀ a,0≤w a)
    (hw1 : ∑ a,w a=1) (p : ℕ → ℝ) (hp0 : ∀ i,0≤p i)
    (hp : Summable p) (hp1 : (∑' i,p i)=1)
    (hh : Summable (fun i => entropyTerm (p i))) :
    (∑' n,entropyTerm (eigenvalue d w p n))=
      (∑' i,entropyTerm (p i))+∑ a,entropyTerm (w a) := by
  have hs (a : Fin d) : Summable (fun i => entropyTerm (w a*p i)) := by
    simp_rw [entropyTerm_mul _ _ (hw0 a) (hp0 _)]
    exact (hh.mul_left (w a)).add (hp.mul_right (entropyTerm (w a)))
  have he (a : Fin d) : (∑' i,entropyTerm (w a*p i))=
      w a*(∑' i,entropyTerm (p i))+entropyTerm (w a) := by
    simp_rw [entropyTerm_mul _ _ (hw0 a) (hp0 _)]
    rw [Summable.tsum_add (hh.mul_left _) (hp.mul_right _),tsum_mul_left,
      tsum_mul_right,hp1,one_mul]
  rw [← (coordinates d).tsum_eq]
  simp only [eigenvalue,Equiv.symm_apply_apply]
  rw [(finite_family_summable d (fun a i => entropyTerm (w a*p i)) hs).tsum_prod,tsum_fintype]
  simp_rw [he]
  rw [Finset.sum_add_distrib,← Finset.sum_mul,hw1,one_mul]

theorem density_spectral (w : Fin d → ℝ) (hw0 : ∀ a,0≤w a) (hw1 : ∑ a,w a=1)
    (h : Density) (p : ℕ → ℝ) (u : ℕ → H) (hp0 : ∀ i,0≤p i)
    (hp : Summable p) (hu : Orthonormal ℂ u)
    (he : ∀ v,h.op v=∑' i,((p i:ℂ)*inner ℂ (u i) v) • u i) (v : H) :
    (weightedDensity d w hw0 hw1 h).op v=
      ∑' n,((eigenvalue d w p n:ℂ)*inner ℂ (FiniteAncilla.eigenvector d u n) v) •
        FiniteAncilla.eigenvector d u n := by
  have hp' : ∀ n,0≤eigenvalue d w p n := fun n => mul_nonneg (hw0 _) (hp0 _)
  have hs := spectral_series_summable (eigenvalue d w p) (FiniteAncilla.eigenvector d u)
    hp' (eigenvalue_summable d w p hp) (eigenvector_orthonormal d u hu) v
  apply ext_fiber (coordinates d)
  intro a
  change fiber (coordinates d) (weightedOp d w h.op v) a=
    project (coordinates d) a (∑' n,
      ((eigenvalue d w p n:ℂ)*inner ℂ (FiniteAncilla.eigenvector d u n) v) •
        FiniteAncilla.eigenvector d u n)
  rw [(project (coordinates d) a).map_tsum hs]
  rw [← (coordinates d).tsum_eq]
  have hsprod := ((hs.hasSum.mapL (project (coordinates d) a)).summable).comp_injective
    (coordinates d).injective
  dsimp only [Function.comp_def] at hsprod
  rw [hsprod.tsum_prod,tsum_fintype]
  simp only [eigenvalue,FiniteAncilla.eigenvector,Equiv.symm_apply_apply,map_smul,
    project_apply,fiber_insert,insert_inner]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true,weighted_fiber,he]
    rw [← (spectral_series_summable p u hp0 hp hu (fiber (coordinates d) v a)).tsum_const_smul (w a:ℂ)]
    apply tsum_congr
    intro i
    push_cast
    rw [smul_smul]
    congr 1
    ring
  · intro b hb hba
    simp only [if_neg (Ne.symm hba),smul_zero,tsum_zero]
  · simp

theorem weighted_finite_entropy (w : Fin d → ℝ) (hw0 : ∀ a,0≤w a) (hw1 : ∑ a,w a=1)
    (h : Density) (hh : FiniteDensityEntropy h) :
    FiniteDensityEntropy (weightedDensity d w hw0 hw1 h) := by
  obtain ⟨p,u,hp0,hp,hp1,hu,he,hent⟩ := hh
  exact ⟨eigenvalue d w p,FiniteAncilla.eigenvector d u,
    fun n => mul_nonneg (hw0 _) (hp0 _),eigenvalue_summable d w p hp,
    eigenvalue_sum d w hw1 p hp hp1,eigenvector_orthonormal d u hu,
    density_spectral d w hw0 hw1 h p u hp0 hp hu he,
    eigenvalue_entropy_summable d w hw0 p hp0 hp hent⟩

theorem scaffold_finite_entropy (h : Density) (hh : FiniteDensityEntropy h) :
    FiniteDensityEntropy (scaffoldDensity h) := by
  apply weighted_finite_entropy 17
  exact hh

theorem scaffold_qutrit_finite_entropy (h : Density) (hh : FiniteDensityEntropy h) :
    FiniteDensityEntropy (FiniteAncilla.density 3 (scaffoldDensity h)) :=
  FiniteAncilla.finiteDensityEntropy 3 _ (scaffold_finite_entropy h hh)

#print axioms weighted_finite_entropy
#print axioms eigenvalue_entropy_sum
#print axioms scaffold_qutrit_finite_entropy
end Sigma2.CompilerHonestDensityEntropy
