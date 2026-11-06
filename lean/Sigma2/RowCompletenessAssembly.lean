import Sigma2.FiniteAncillaEntropy
import Sigma2.RowGame

/-! The analytic assembly step for a concrete row-game POVM assignment.
The remaining hypotheses concern only the supplied local POVMs and concrete rejections. -/
set_option maxHeartbeats 300000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.FiniteAncilla
open Coefficients TensorLifts
variable (d : ℕ) [NeZero d]

/-- Any new finite scenario can use this same enlarged ensemble. -/
def withMeasurements {s t} (S : NormalStrategy s) (M : Measurements t) : NormalStrategy t where
  measurements := M
  vector k := entangle d (S.vector k)
  unit k := by rw [(entangle d).norm_map,S.unit k]
  weight := S.weight
  weight_nonneg := S.weight_nonneg
  weight_summable := S.weight_summable
  weight_sum := S.weight_sum

theorem withMeasurements_marginalA {s t} (S : NormalStrategy s) (M : Measurements t)
    (h : Density) (hm : MarginalA S h) : MarginalA (withMeasurements d S M) (density d h) :=
  marginalA d S h hm

theorem withMeasurements_marginalB {s t} (S : NormalStrategy s) (M : Measurements t)
    (h : Density) (hm : MarginalB S h) : MarginalB (withMeasurements d S M) (density d h) :=
  marginalB d S h hm

theorem withMeasurements_entropy {s t} (S : NormalStrategy s) (M : Measurements t)
    (hh : FiniteMarginalEntropy S) : FiniteMarginalEntropy (withMeasurements d S M) := by
  obtain ⟨hA,hB,hmA,hmB,hhA,hhB⟩ := hh
  exact ⟨density d hA,density d hB,withMeasurements_marginalA d S M hA hmA,
    withMeasurements_marginalB d S M hB hmB,finiteDensityEntropy d hA hhA,
    finiteDensityEntropy d hB hhB⟩

theorem withMeasurements_extends {s t} (E : Compiler.ScenarioEmbedding s t)
    (S : NormalStrategy s) (M : Measurements t)
    (hA : ∀ x a,M.alice (E.qA x) (E.aA a)=amplify d (S.measurements.alice x a))
    (hB : ∀ y b,M.bob (E.qB y) (E.aB b)=amplify d (S.measurements.bob y b)) :
    Compiler.Extends E S (withMeasurements d S M) := by
  intro x y a b
  unfold NormalStrategy.probability
  apply tsum_congr
  intro k
  change S.weight k*(S.component k).probability x y a b=
    S.weight k*((withMeasurements d S M).component k).probability (E.qA x) (E.qB y) (E.aA a) (E.aB b)
  congr 1
  change (inner ℂ (S.vector k) ((S.measurements.left x a*S.measurements.right y b) (S.vector k))).re=
    (inner ℂ (entangle d (S.vector k))
      ((M.left (E.qA x) (E.aA a)*M.right (E.qB y) (E.aB b)) (entangle d (S.vector k)))).re
  rw [measurements_left,measurements_right,measurements_left,measurements_right,hA,hB]
  change _=(inner ℂ (entangle d (S.vector k))
    (left (amplify d (S.measurements.alice x a))
      (right (amplify d (S.measurements.bob y b)) (entangle d (S.vector k))))).re
  rw [right_entangle,left_entangle,(entangle d).inner_map_map]
  rfl

/-- Killing each positive-weight component proves an actual ensemble event zero. -/
theorem withMeasurements_zero {s t} (S : NormalStrategy s) (M : Measurements t)
    (x y a b)
    (hz : ∀ k,0<S.weight k →
      (M.left x a*M.right y b) (entangle d (S.vector k))=0) :
    (withMeasurements d S M).probability x y a b=0 := by
  unfold NormalStrategy.probability
  trans ∑' k : ℕ,(0:ℝ)
  · apply tsum_congr
    intro k
    by_cases hk : 0<S.weight k
    · change S.weight k*(inner ℂ (entangle d (S.vector k))
        ((M.left x a*M.right y b) (entangle d (S.vector k)))).re=0
      rw [hz k hk,inner_zero_right,Complex.zero_re,mul_zero]
    · have hw : S.weight k=0 := le_antisymm (not_lt.mp hk) (S.weight_nonneg k)
      change S.weight k*_=0
      rw [hw,zero_mul]
  · exact tsum_zero

theorem withMeasurements_perfect {s} (G : Game) (S : NormalStrategy s)
    (M : Measurements G.scenario)
    (hz : ∀ x y a b,G.accepts x y a b=false → ∀ k,0<S.weight k →
      (M.left x a*M.right y b) (entangle d (S.vector k))=0) :
    Perfect G (withMeasurements d S M) := by
  unfold Perfect loss
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  cases h : G.accepts x y a b
  · simp only [Bool.false_eq_true,ite_false]
    rw [withMeasurements_zero d S M x y a b (hz x y a b h),mul_zero]
  · simp

end Sigma2.FiniteAncilla

namespace Sigma2.RowCompleteness
open Compiler RowGame FiniteAncilla

local instance assemblyDimensionNeZero {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

/-- Once the simultaneous concrete local POVMs and rejected vector products
have been proved, no further spatial, ensemble, correlation or entropy work remains.
This is an assembly theorem, not the unresolved completeness construction. -/
theorem completeness_of_measurements (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy G.scenario) (M : Measurements (scenario G R))
    (hA : ∀ x a,M.alice ((embedding G R).qA x) ((embedding G R).aA a)=
      amplify (RowSlots.dimension R) (S.measurements.alice x a))
    (hB : ∀ y b,M.bob ((embedding G R).qB y) ((embedding G R).aB b)=
      amplify (RowSlots.dimension R) (S.measurements.bob y b))
    (hz : ∀ x y a b,(game G R).accepts x y a b=false → ∀ k,0<S.weight k →
      (M.left x a*M.right y b) (entangle (RowSlots.dimension R) (S.vector k))=0) :
    ∃ T : NormalStrategy (scenario G R),Perfect (game G R) T ∧
      Extends (embedding G R) S T ∧ (FiniteMarginalEntropy S → FiniteMarginalEntropy T) := by
  exact ⟨withMeasurements (RowSlots.dimension R) S M,
    withMeasurements_perfect (RowSlots.dimension R) (game G R) S M hz,
    withMeasurements_extends (RowSlots.dimension R) (embedding G R) S M hA hB,
    withMeasurements_entropy (RowSlots.dimension R) S M⟩

end Sigma2.RowCompleteness
