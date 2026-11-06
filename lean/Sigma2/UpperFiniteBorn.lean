import Sigma2.UpperSchmidtState
import Sigma2.UpperFiniteAmplitudes

set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSimpArgs false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.UpperFiniteBorn
open UpperFiniteOperators UpperFiniteAmplitudes

/-- A finite coordinate support turns the infinite sum into the indicated finite sum. -/
theorem tsum_fin {V : Type} [NormedAddCommGroup V] (m : ℕ) (f : ℕ → V)
    (hz : ∀ i,m ≤ i → f i=0) : (∑' i,f i)=∑ i : Fin m,f i := by
  rw [tsum_eq_sum (s := Finset.range m) (fun i hi => hz i (by simpa using hi))]
  exact (Fin.sum_univ_eq_sum_range f m).symm

theorem summable_fin {V : Type} [NormedAddCommGroup V] (m : ℕ) (f : ℕ → V)
    (hz : ∀ i,m ≤ i → f i=0) : Summable f :=
  (hasSum_sum_of_ne_finset_zero (s := Finset.range m)
    (fun i hi => hz i (by simpa using hi))).summable

theorem pad_sum (m : ℕ) (p : Fin m → ℝ) :
    (∑' i,pad m p i)=∑ i,p i := by
  rw [tsum_fin m _ (pad_zero m p)]
  simp

theorem pad_summable (m : ℕ) (p : Fin m → ℝ) : Summable (pad m p) :=
  summable_fin m _ (pad_zero m p)

/-- The reduced density used by Schmidt transport is the actual frozen marginal. -/
theorem density_marginal {s} (S : PureStrategy s) :
    MarginalA (normalOfPure S) (UpperSchmidtSpectrum.density S.vector S.unit) := by
  intro i j
  change Coefficients.covariance (Coefficients.column S.vector) (basis j) i = _
  rw [show basis j=lp.single 2 j 1 from rfl,
    Coefficients.covariance_entry _ (Coefficients.column_mass S.vector).1]
  simp [normalOfPure,Coefficients.column_apply,apply_ite,ite_mul]

theorem marginal_op_eq {s} (S : PureStrategy s) (h : Density)
    (hh : MarginalA (normalOfPure S) h) :
    h.op=(UpperSchmidtSpectrum.density S.vector S.unit).op := by
  apply UpperAnalytic.entry_ext
  intro i j
  exact (hh i j).trans (density_marginal S i j).symm

/-- The finite Born expression is evaluated on a diagonal, finitely supported vector. -/
theorem diagonal_inner (m : ℕ) (t : Fin m → ℝ) (v w : AB)
    (hv : ∀ i j,v (i,j)=if i=j then (pad m t i:ℂ) else 0) :
    inner ℂ v w=∑ i : Fin m,(t i:ℂ)*w (i,i) := by
  change (∑' ij : ℕ × ℕ,w ij*star (v ij))=_
  have hz (ij : ℕ × ℕ) (hij : ij ∉ (Finset.range m).product (Finset.range m)) :
      w ij*star (v ij)=0 := by
    rcases ij with ⟨i,j⟩
    rw [hv]
    by_cases he : i=j
    · subst j
      have hi : m ≤ i := by simpa using hij
      simp [pad_zero m t i hi]
    · simp [he]
  rw [tsum_eq_sum hz]
  change (∑ ij ∈ (Finset.range m).product (Finset.range m),
    w ij*star (v ij))=_
  erw [Finset.sum_product]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.sum_eq_single i]
  · simp [hv,mul_comm]
  · intro j _ hji
    have hij : (i:ℕ)≠j := fun h => hji (Fin.ext h.symm)
    simp [hv,hij]
  · simp

theorem diagonal_event {s} (M : Measurements s) (m : ℕ) (t : Fin m → ℝ)
    (v : AB) (hv : ∀ i j,v (i,j)=if i=j then (pad m t i:ℂ) else 0)
    (x : QA s) (y : QB s) (a : AA s) (b : BB s) :
    inner ℂ v ((M.left x a*M.right y b) v)=
      ∑ i : Fin m,∑ j : Fin m,(t i:ℂ)*(t j:ℂ)*
        compress m (M.alice x a) i j*compress m (M.bob y b) i j := by
  rw [diagonal_inner m t v _ hv]
  apply Finset.sum_congr rfl
  intro i _
  change (t i:ℂ)*(M.left x a (M.right y b v)) (i,i)=_
  rw [M.left_coordinates]
  have hr (j : ℕ) : (M.right y b v) (j,i)=
      entry (M.bob y b) i j*(pad m t j:ℂ) := by
    rw [M.right_coordinates]
    simp only [hv,mul_ite,mul_zero,tsum_ite_eq']
  simp_rw [hr]
  rw [tsum_fin m _ (fun j hj => by simp [pad_zero m t j hj]),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [pad_fin,compress]
  ring

/-- Loss is precisely the finite polynomial Born expression, with the genuine Bob entries. -/
theorem diagonal_loss (G : Game) (S : PureStrategy G.scenario) (m : ℕ)
    (t : Fin m → ℝ)
    (hv : ∀ i j,S.vector (i,j)=if i=j then (pad m t i:ℂ) else 0) :
    loss G (normalOfPure S)=
      ∑ x,∑ y,∑ a,∑ b,if G.accepts x y a b then 0 else
        (G.distribution x y:ℝ)*(∑ i : Fin m,∑ j : Fin m,
          (t i:ℂ)*(t j:ℂ)*compress m (S.measurements.alice x a) i j*
            compress m (S.measurements.bob y b) i j).re := by
  simp only [loss,normalOfPure_probability,PureStrategy.probability,
    diagonal_event S.measurements m t S.vector hv]
  congr 1
  funext x
  congr 1
  funext y
  congr 1
  funext a
  congr 1
  funext b
  cases G.accepts x y a b <;> simp

/-- Compression of an extended finite POVM, including the complementary deterministic answer. -/
theorem compress_effect {ι : Type} [DecidableEq ι] (m : ℕ) (a₀ a : ι)
    (A : Matrix (Fin m) (Fin m) ℂ) : compress m (effect m a₀ a A)=A := by
  ext i j
  simp only [compress,effect,entry,add_apply,lp.coeFn_add,Pi.add_apply]
  change entry (extend m A) i j+_=A i j
  rw [extend_entry_fin]
  suffices (if a=a₀ then 1-cut m else 0 : Op) (basis j) i=0 by rw [this,add_zero]
  split_ifs
  · simp [cut_apply,j.isLt,i.isLt]
  · rfl

end Sigma2.UpperFiniteBorn








