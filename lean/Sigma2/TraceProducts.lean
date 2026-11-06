import Sigma2.PureTransfer
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.TraceProducts
open Coefficients

theorem image_summable {ι : Type} (B : Op) (u : ι → H)
    (hu : Summable (fun k => ‖u k‖^2)) : Summable (fun k => ‖B (u k)‖^2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun k => ?_)
    (hu.mul_left (‖B‖^2))
  calc
    _ ≤ (‖B‖*‖u k‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm _) 2
    _ = _ := mul_pow _ _ _

/-- Absolute summability of the full diagonal/ensemble double sum. -/
theorem cross_summable {ι : Type} (u v : ι → H)
    (hu : Summable (fun k => ‖u k‖^2)) (hv : Summable (fun k => ‖v k‖^2)) :
    Summable (fun ki : ι × ℕ => u ki.1 ki.2*star (v ki.1 ki.2)) := by
  apply Summable.of_norm_bounded
    ((coefficient_mass_summable u hu).add (coefficient_mass_summable v hv))
  intro ki
  rw [norm_mul,norm_star]
  nlinarith [sq_nonneg (‖u ki.1 ki.2‖-‖v ki.1 ki.2‖)]

theorem covariance_mul_entry {ι : Type} (u : ι → H)
    (hu : Summable (fun k => ‖u k‖^2)) (B : Op) (hB : Positive B) (i : ℕ) :
    entry (covariance u*B) i i=∑' k,u k i*star (B (u k) i) := by
  have hh := covariance_hasSum u hu (basis i) (B (basis i))
  have he k : inner ℂ (basis i) (u k)*inner ℂ (u k) (B (basis i))=
      u k i*star (B (u k) i) := by
    calc
      _ = inner ℂ (basis i) (u k)*inner ℂ (B (u k)) (basis i) :=
        congrArg (fun z : ℂ => inner ℂ (basis i) (u k)*z)
          (hB.isSymmetric (u k) (basis i)).symm
      _ = _ := by
        simp [basis,lp.inner_single_left,lp.inner_single_right,RCLike.inner_apply,RCLike.star_def]
  calc
    _ = inner ℂ (basis i) (covariance u (B (basis i))) := by
      simp [entry,basis,lp.inner_single_left,RCLike.inner_apply]
    _ = ∑' k,inner ℂ (basis i) (u k)*inner ℂ (u k) (B (basis i)) := hh.tsum_eq.symm
    _ = _ := tsum_congr he

/-- Trace-product identity for the original diagonal-tsum trace. The proof uses
absolute double summability, never operator-norm continuity of trace. -/
theorem covariance_mul_trace {ι : Type} (u : ι → H)
    (hu : Summable (fun k => ‖u k‖^2)) (B : Op) (hB : Positive B) :
    Summable (fun i => entry (covariance u*B) i i) ∧
      trace (covariance u*B)=∑' k,inner ℂ (B (u k)) (u k) ∧
      Summable (fun k => inner ℂ (B (u k)) (u k)) := by
  have hs := cross_summable u (fun k => B (u k)) hu (image_summable B u hu)
  have he k : (∑' i,u k i*star (B (u k) i))=inner ℂ (B (u k)) (u k) := by
    rw [lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    simp only [RCLike.inner_apply,RCLike.star_def,mul_comm]
  refine ⟨?_,?_,?_⟩
  · simp_rw [covariance_mul_entry u hu B hB]
    exact hs.prod_symm.prod
  · unfold trace
    simp_rw [covariance_mul_entry u hu B hB]
    have hs' : Summable (Function.uncurry (fun k i => u k i*star (B (u k) i))) := hs
    have hc := hs'.tsum_comm
    rw [hc]
    exact tsum_congr he
  · simpa only [he] using hs.prod

def rootFamily (h : Density) (k : ℕ) : H := positiveRoot h.op (basis k)

theorem root_summable (h : Density) : Summable (fun k => ‖rootFamily h k‖^2) := by
  have he k : ‖rootFamily h k‖^2=(entry h.op k k).re := by
    simpa [rootFamily,basis,entry,lp.inner_single_left,RCLike.inner_apply] using
      sqrt_column_norm_sq h.op h.positive k
  simpa only [he] using h.diagonal_summable

theorem density_eq_covariance (h : Density) : h.op=covariance (rootFamily h) := by
  symm
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  exact (covariance_hasSum (rootFamily h) (root_summable h) w v).tsum_eq.symm.trans
    (sqrt_columns h.op h.positive w v).tsum_eq

theorem zero_trace_columns (h : Density) (B : Op) (hB : Positive B)
    (hz : (trace (h.op*B)).re=0) :
    ∀ k,(inner ℂ (B (rootFamily h k)) (rootFamily h k)).re=0 := by
  have ht := covariance_mul_trace (rootFamily h) (root_summable h) B hB
  have hh := ht.2.2.hasSum.mapL Complex.reCLM
  have he : (∑' k,inner ℂ (B (rootFamily h k)) (rootFamily h k)).re=0 := by
    rw [← ht.2.1,← density_eq_covariance]
    exact hz
  change HasSum (fun k => (inner ℂ (B (rootFamily h k)) (rootFamily h k)).re)
    (∑' k,inner ℂ (B (rootFamily h k)) (rootFamily h k)).re at hh
  rw [he] at hh
  exact fun k => congrFun
    ((hasSum_zero_iff_of_nonneg (fun j => hB.re_inner_nonneg_left _)).mp hh) k

#print axioms covariance_mul_trace
#print axioms zero_trace_columns
end Sigma2.TraceProducts
