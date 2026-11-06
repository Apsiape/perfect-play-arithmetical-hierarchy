import Sigma2.UpperFiniteBorn

set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.UpperEntropyFinite
open UpperFiniteOperators UpperFiniteAmplitudes UpperFiniteBorn

abbrev Data (s : Scenario) (m : ℕ) :=
  (Fin m → ℝ) × (Fin m → ℝ) ×
    (QA s → AA s → Matrix (Fin m) (Fin m) ℂ) ×
    (QB s → BB s → Matrix (Fin m) (Fin m) ℂ)

def finiteLoss (G : Game) (m : ℕ) (z : Data G.scenario m) : ℝ :=
  ∑ x,∑ y,∑ a,∑ b,if G.accepts x y a b then 0 else
    (G.distribution x y:ℝ)*(∑ i,∑ j,
      (z.2.1 i:ℂ)*(z.2.1 j:ℂ)*z.2.2.1 x a i j*z.2.2.2 y b i j).re

def Feasible (G : Game) (m : ℕ) (η : ℝ) (z : Data G.scenario m) : Prop :=
  (∀ i,0 ≤ z.1 i) ∧ (∑ i,z.1 i)=1 ∧ Antitone z.1 ∧
    (∀ i,0 ≤ z.2.1 i ∧ z.2.1 i^2=z.1 i) ∧
    (∀ x a,(z.2.2.1 x a).PosSemidef) ∧ (∀ y b,(z.2.2.2 y b).PosSemidef) ∧
    (∀ x,∑ a,z.2.2.1 x a=1) ∧ (∀ y,∑ b,z.2.2.2 y b=1) ∧ finiteLoss G m z ≤ η

theorem basis_orthonormal : Orthonormal ℂ basis := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [basis,lp.inner_single_left,lp.single_apply,Pi.single_apply,eq_comm]

/-- The actual reduced density of the canonical state has the prescribed diagonal. -/
theorem canonical_diagonal (q : ℕ → ℝ) (hq : ∀ i,0 ≤ q i) (hs : Summable q)
    (ht : (∑' i,q i)=1) :
    UpperAmplitudes.Diagonal
      (UpperSchmidtSpectrum.density (UpperSchmidtState.vector q hq hs)
        (UpperSchmidtState.vector_unit q hq hs ht)).op q := by
  intro i j
  change Coefficients.covariance (Coefficients.column (UpperSchmidtState.vector q hq hs))
    (basis j) i=if i=j then (q i:ℂ) else 0
  rw [show basis j=lp.single 2 j 1 from rfl,
    Coefficients.covariance_entry _ (Coefficients.column_mass _).1]
  simp only [Coefficients.column_apply,UpperSchmidtState.vector_apply]
  rw [tsum_eq_single i]
  · by_cases hij : i=j
    · subst j
      simp only [ite_true]
      rw [show star (Real.sqrt (q i):ℂ)=(Real.sqrt (q i):ℂ) by simp,
        ← Complex.ofReal_mul,← pow_two,Real.sq_sqrt (hq i)]
    · simp [hij,Ne.symm hij]
  · intro k hk
    simp [Ne.symm hk]

/-- Finite square roots and measurements are extracted without changing any event. -/
theorem data_of_spectrum (G : Game) (m : ℕ) (η : ℝ)
    (S : PureStrategy G.scenario) (hl : loss G (normalOfPure S) ≤ η)
    (h : Density) (hm : MarginalA (normalOfPure S) h)
    (p : ℕ → ℝ) (u : ℕ → H) (hp : ∀ i,0 ≤ p i) (hs : Summable p)
    (ht : (∑' i,p i)=1) (ha : Antitone p) (hu : Orthonormal ℂ u)
    (hz : ∀ i,m ≤ i → p i=0)
    (he : ∀ v,h.op v=∑' i,((p i:ℂ)*inner ℂ (u i) v) • u i) :
    ∃ z : Data G.scenario m,Feasible G m η z ∧ ∀ i,z.1 i=p i := by
  have he' : ∀ v,(UpperSchmidtSpectrum.density S.vector S.unit).op v=
      ∑' i,((p i:ℂ)*inner ℂ (u i) v) • u i := by
    rw [← marginal_op_eq S h hm]
    exact he
  obtain ⟨T,hTv,hprob⟩ := UpperSchmidtState.exists_strategy S p u hp hs ht hu he'
  let t : Fin m → ℝ := fun i => Real.sqrt (p i)
  have hpad i : pad m t i=Real.sqrt (p i) := by
    by_cases hi : i<m
    · simp [pad,t,hi]
    · simp [pad,hi,hz i (Nat.le_of_not_gt hi)]
  have hv i j : T.vector (i,j)=if i=j then (pad m t i:ℂ) else 0 := by
    rw [hTv,UpperSchmidtState.vector_apply,hpad]
  have hsum : (∑ i : Fin m,p i)=1 := (tsum_fin m p hz).symm.trans ht
  let z : Data G.scenario m := (fun i => p i,t,
    fun x a => compress m (T.measurements.alice x a),
    fun y b => compress m (T.measurements.bob y b))
  refine ⟨z,⟨(fun i => hp i),hsum,(fun i j hij => ha hij),
    (fun i => ⟨Real.sqrt_nonneg _,Real.sq_sqrt (hp i)⟩),
    (fun x a => compress_positive _ _ (T.measurements.alice_pos x a)),
    (fun y b => compress_positive _ _ (T.measurements.bob_pos y b)),
    (fun x => compress_sum _ _ (T.measurements.alice_sum x)),
    (fun y => compress_sum _ _ (T.measurements.bob_sum y)),?_⟩,fun _ => rfl⟩
  have heq : loss G (normalOfPure T)=loss G (normalOfPure S) := by
    simp only [loss,normalOfPure_probability]
    simp_rw [hprob]
  exact (diagonal_loss G T m t hv).symm.trans_le (heq.trans_le hl)

end Sigma2.UpperEntropyFinite




