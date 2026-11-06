import Sigma2.UpperEntropyFinite

set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.UpperEntropyCanonical
open UpperFiniteOperators UpperFiniteAmplitudes UpperFiniteBorn UpperEntropyFinite

/-- The same genuine marginal formula holds for an infinite canonical spectrum. -/
theorem spectral_infinite (q : ℕ → ℝ) (hq : ∀ i,0 ≤ q i)
    (hs : Summable q) (ht : (∑' i,q i)=1) (v : H) :
    (UpperSchmidtSpectrum.density (UpperSchmidtState.vector q hq hs)
      (UpperSchmidtState.vector_unit q hq hs ht)).op v=
        ∑' i,((q i:ℂ)*inner ℂ (basis i) v) • basis i := by
  let h := UpperSchmidtSpectrum.density (UpperSchmidtState.vector q hq hs)
    (UpperSchmidtState.vector_unit q hq hs ht)
  have hh := (lp.hasSum_single (by norm_num : (2:ENNReal)≠⊤) (h.op v)).tsum_eq
  exact hh.symm.trans (tsum_congr fun i => by
    have hc : inner ℂ (basis i) v=v i := by simp [basis,lp.inner_single_left]
    rw [hc,UpperAmplitudes.diagonal_apply (canonical_diagonal q hq hs ht)]
    simp only [basis,← lp.single_smul,smul_eq_mul,mul_one])

/-- The two marginals of a canonical Schmidt vector are the same actual density. -/
theorem marginalB {s} (M : Measurements s) (q : ℕ → ℝ) (hq : ∀ i,0 ≤ q i)
    (hs : Summable q) (ht : (∑' i,q i)=1) :
    MarginalB (normalOfPure (⟨M,UpperSchmidtState.vector q hq hs,
      UpperSchmidtState.vector_unit q hq hs ht⟩ : PureStrategy s))
      (UpperSchmidtSpectrum.density (UpperSchmidtState.vector q hq hs)
        (UpperSchmidtState.vector_unit q hq hs ht)) := by
  let S : PureStrategy s := ⟨M,UpperSchmidtState.vector q hq hs,
    UpperSchmidtState.vector_unit q hq hs ht⟩
  have hv i j : S.vector (i,j)=S.vector (j,i) := by
    change UpperSchmidtState.vector q hq hs (i,j)=UpperSchmidtState.vector q hq hs (j,i)
    by_cases hij : i=j
    · simp [hij]
    · simp [hij,Ne.symm hij]
  intro i j
  rw [density_marginal S i j]
  apply tsum_congr
  intro k
  apply congrArg (fun z : ℂ => ((normalOfPure S).weight k:ℂ)*z)
  apply tsum_congr
  intro a
  change S.vector (i,a)*star (S.vector (j,a))=S.vector (a,i)*star (S.vector (a,j))
  rw [hv i a,hv j a]

/-- Summable canonical entropy realizes both frozen marginal-entropy requirements. -/
theorem finite_marginal_entropy {s} (M : Measurements s) (q : ℕ → ℝ)
    (hq : ∀ i,0 ≤ q i) (hs : Summable q) (ht : (∑' i,q i)=1)
    (hH : Summable (fun i => entropyTerm (q i))) :
    FiniteMarginalEntropy (normalOfPure (⟨M,UpperSchmidtState.vector q hq hs,
      UpperSchmidtState.vector_unit q hq hs ht⟩ : PureStrategy s)) := by
  let S : PureStrategy s := ⟨M,UpperSchmidtState.vector q hq hs,
    UpperSchmidtState.vector_unit q hq hs ht⟩
  let h := UpperSchmidtSpectrum.density S.vector S.unit
  have he : FiniteDensityEntropy h :=
    ⟨q,basis,hq,hs,ht,basis_orthonormal,spectral_infinite q hq hs ht,hH⟩
  exact ⟨h,h,density_marginal S,marginalB M q hq hs ht,he,he⟩

/-- A finite canonical diagonal state has exactly its specified padded spectrum. -/
theorem spectral (m : ℕ) (q : ℕ → ℝ) (hq : ∀ i,0 ≤ q i)
    (hs : Summable q) (ht : (∑' i,q i)=1) (hz : ∀ i,m ≤ i → q i=0) (v : H) :
    (UpperSchmidtSpectrum.density (UpperSchmidtState.vector q hq hs)
      (UpperSchmidtState.vector_unit q hq hs ht)).op v=
        ∑' i,((q i:ℂ)*inner ℂ (basis i) v) • basis i := by
  rw [tsum_fin m _ (fun i hi => by simp [hz i hi])]
  ext k
  rw [UpperAmplitudes.diagonal_apply (canonical_diagonal q hq hs ht)]
  have he : (∑ i : Fin m,((q i:ℂ)*inner ℂ (basis i) v) • basis i) k=
      if hk : k<m then (q k:ℂ)*v k else 0 := by
    simp only [lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,
      smul_eq_mul,basis,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,
      lp.single_apply,Pi.single_apply]
    simpa only [eq_comm,mul_ite,mul_one,mul_zero] using
      sum_nat_eq m k (fun i => (q i:ℂ)*v i)
  rw [he]
  by_cases hk : k<m
  · simp [hk]
  · simp [hk,hz k (Nat.le_of_not_gt hk)]

/-- Finite feasible matrices reconstruct a normalized state, its true marginal,
and the desired spectrum. Complementary answers make both infinite POVMs unital. -/
theorem strategy_of_feasible (G : Game) (m : ℕ) (η : ℝ)
    (z : Data G.scenario m) (hf : Feasible G m η z) :
    ∃ S : PureStrategy G.scenario,FiniteSupport S m ∧ loss G (normalOfPure S) ≤ η ∧
      ∃ h : Density,MarginalA (normalOfPure S) h ∧
        ∀ v,h.op v=∑' i,((pad m z.1 i:ℂ)*inner ℂ (basis i) v) • basis i := by
  obtain ⟨hp,hs,ha,ht,hE,hF,hEs,hFs,hl⟩ := hf
  let q := pad m z.1
  have hq : ∀ i,0 ≤ q i := pad_nonneg m z.1 hp
  have hqs : Summable q := pad_summable m z.1
  have hqt : (∑' i,q i)=1 := (pad_sum m z.1).trans hs
  let M : Measurements G.scenario := TensorLifts.measurements G.scenario
    (fun x a => effect m 0 a (z.2.2.1 x a))
    (fun y b => effect m 0 b (z.2.2.2 y b))
    (fun x a => effect_positive m 0 a _ (hE x a))
    (fun y b => effect_positive m 0 b _ (hF y b))
    (fun x => effect_sum m 0 _ (hEs x))
    (fun y => effect_sum m 0 _ (hFs y))
  let S : PureStrategy G.scenario :=
    ⟨M,UpperSchmidtState.vector q hq hqs,UpperSchmidtState.vector_unit q hq hqs hqt⟩
  have hroot i : z.2.1 i=Real.sqrt (z.1 i) := by
    nlinarith [(ht i).1,(ht i).2,Real.sqrt_nonneg (z.1 i),Real.sq_sqrt (hp i)]
  have hpad i : pad m z.2.1 i=Real.sqrt (q i) := by
    by_cases hi : i<m
    · simp [q,pad,hi,hroot]
    · simp [q,pad,hi]
  have hv i j : S.vector (i,j)=if i=j then (pad m z.2.1 i:ℂ) else 0 := by
    change UpperSchmidtState.vector q hq hqs (i,j)=_
    rw [UpperSchmidtState.vector_apply,hpad]
  have hloss : loss G (normalOfPure S)=finiteLoss G m z := by
    rw [diagonal_loss G S m z.2.1 hv]
    simp only [S,M,TensorLifts.measurements,compress_effect,finiteLoss]
  refine ⟨S,?_,hloss.trans_le hl,
    UpperSchmidtSpectrum.density S.vector S.unit,density_marginal S,?_⟩
  · intro i j hij
    rw [hv]
    by_cases he : i=j
    · subst j
      simp [pad_zero m z.2.1 i (hij.elim id id)]
    · simp [he]
  · exact spectral m q hq hqs hqt (pad_zero m z.1)

end Sigma2.UpperEntropyCanonical

