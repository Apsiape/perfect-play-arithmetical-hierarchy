import Sigma2.FockModel
import Sigma2.EntropyTrace

/-! Trace, faithfulness and entropy witnesses for summable diagonal densities. -/
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal Classical
namespace Sigma2.FockModel

lemma diagonal_entry (c : ℕ → ℂ) (hc : Bounded c) (i : ℕ) :
    entry (diagonal c hc) i i=c i := by
  simp [entry,Sigma2.basis,lp.single_apply]

/-- The ambient trace agrees with the diagonal sum. -/
lemma diagonal_trace (c : ℕ → ℂ) (hc : Bounded c) :
    trace (diagonal c hc)=∑' i,c i := by
  simp only [trace,diagonal_entry]

lemma probability_bounded (p : ℕ → ℝ) (hp : ∀ i, 0≤p i)
    (hs : Summable p) (hm : (∑' i,p i)=1) : Bounded (fun i => (p i : ℂ)) := by
  refine ⟨1,fun i => ?_⟩
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp i)]
  rw [← hm]
  exact hs.le_tsum i (fun j _ => hp j)

/-- A diagonal probability law gives an actual positive trace-one operator. -/
def diagonalDensity (p : ℕ → ℝ) (hp : ∀ i, 0≤p i)
    (hs : Summable p) (hm : (∑' i,p i)=1) : Density where
  op := diagonal (fun i => (p i : ℂ)) (probability_bounded p hp hs hm)
  positive := diagonal_positive p hp _
  diagonal_summable := by simpa only [diagonal_entry,Complex.ofReal_re] using hs
  trace_one := by simpa only [diagonal_entry,Complex.ofReal_re] using hm

lemma diagonalDensity_faithful (p : ℕ → ℝ) (hp : ∀ i, 0<p i)
    (hs : Summable p) (hm : (∑' i,p i)=1) :
    Faithful (diagonalDensity p (fun i => (hp i).le) hs hm) := by
  intro v w h
  ext i
  have hi := congrArg (fun v : H => v i) h
  change (p i : ℂ)*v i=(p i : ℂ)*w i at hi
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (hp i).ne') hi

/-- The spectral probability and eigenvectors of a diagonal density are explicit.
This proves the operator series, not only summability of scalar entropy terms. -/
lemma diagonalDensity_expansion (p : ℕ → ℝ) (hp : ∀ i, 0≤p i)
    (hs : Summable p) (hm : (∑' i,p i)=1) (v : H) :
    (diagonalDensity p hp hs hm).op v=
      ∑' i,((p i : ℂ)*inner ℂ (Sigma2.basis i) v) • Sigma2.basis i := by
  let b : HilbertBasis ℕ ℂ H := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)
  have hb (i : ℕ) : b i=Sigma2.basis i := b.repr_self i
  have he (i : ℕ) : (diagonalDensity p hp hs hm).op (b i)=(p i : ℂ) • b i :=
    diagonal_single _ _ i
  simpa only [hb] using EntropySpectrum.eigenbasis_expansion (diagonalDensity p hp hs hm) b p he v

lemma diagonalDensity_finiteEntropy (p : ℕ → ℝ) (hp : ∀ i, 0≤p i)
    (hs : Summable p) (hm : (∑' i,p i)=1)
    (he : Summable (fun i => entropyTerm (p i))) :
    FiniteDensityEntropy (diagonalDensity p hp hs hm) := by
  refine ⟨p,Sigma2.basis,hp,hs,hm,?_,diagonalDensity_expansion p hp hs hm,he⟩
  let b : HilbertBasis ℕ ℂ H := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ H)
  have hb : (b : ℕ → H)=Sigma2.basis := funext (fun i => b.repr_self i)
  rw [← hb]
  exact b.orthonormal

#print axioms diagonalDensity_faithful
#print axioms diagonalDensity_finiteEntropy
end Sigma2.FockModel
