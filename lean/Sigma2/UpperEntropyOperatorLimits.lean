import Sigma2.UpperSchmidtOperators
import Sigma2.UpperFiniteAmplitudes

noncomputable section
open scoped BigOperators
open Filter
namespace Sigma2.UpperEntropyOperatorLimits

/-- Pointwise convergence of sorted, uniformly square-summable diagonal amplitudes
is operator-norm convergence. This is the middle-factor limit for entropy sandwiches. -/
theorem diagonal_norm_tendsto (T : ℕ → Op) (D : Op)
    (d : ℕ → ℕ → ℝ) (e : ℕ → ℝ)
    (hd : ∀ n,UpperAmplitudes.Diagonal (T n) (d n)) (he : UpperAmplitudes.Diagonal D e)
    (hp : ∀ n i,0 ≤ d n i) (ha : ∀ n,Antitone (d n))
    (hs : ∀ n,Summable (fun i => d n i^2)) (hb : ∀ n,(∑' i,d n i^2) ≤ 1)
    (hep : ∀ i,0 ≤ e i) (hea : Antitone e)
    (hes : Summable (fun i => e i^2)) (heb : (∑' i,e i^2) ≤ 1)
    (hc : ∀ i,Tendsto (fun n => d n i) atTop (nhds (e i))) :
    Tendsto T atTop (nhds D) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (1/(ε/4)^2)
  have htail (f : ℕ → ℝ) (hf : ∀ i,0 ≤ f i) (hfa : Antitone f)
      (hfs : Summable (fun i => f i^2)) (hfb : (∑' i,f i^2) ≤ 1)
      (i : ℕ) (hi : N ≤ i) : f i ≤ ε/4 := by
    have hh := UpperAnalytic.square_tail f hfa hf hfs 1 hfb i
    apply hh.trans
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    apply (div_le_iff₀ (by positivity : (0:ℝ) < i+1)).mpr
    have hsq : 0 < (ε/4)^2 := by positivity
    have hmul := (div_lt_iff₀ hsq).mp hN
    have hNi : (N:ℝ) ≤ i := by exact_mod_cast hi
    nlinarith
  have hfinite : ∀ᶠ n in atTop,∀ i ∈ Finset.range N,|d n i-e i| < ε/2 := by
    rw [eventually_all_finset]
    intro i _
    obtain ⟨M,hM⟩ := Metric.tendsto_atTop.mp (hc i) (ε/2) (by positivity)
    exact eventually_atTop.mpr ⟨M,fun n hn => by simpa [Real.dist_eq] using hM n hn⟩
  obtain ⟨M,hM⟩ := eventually_atTop.mp hfinite
  refine ⟨M,fun n hn => ?_⟩
  rw [dist_eq_norm]
  have hbound : ‖T n-D‖ ≤ ε/2 := by
    apply UpperAmplitudes.norm_sub_le (hd n) he (ε/2) (by positivity)
    intro i
    by_cases hi : i<N
    · exact le_of_lt (hM n hn i (Finset.mem_range.mpr hi))
    · have hni : N ≤ i := Nat.le_of_not_gt hi
      have hdi := htail (d n) (hp n) (ha n) (hs n) (hb n) i hni
      have hei := htail e hep hea hes heb i hni
      apply abs_le.mpr
      constructor <;> linarith [hp n i,hep i]
  exact hbound.trans_lt (by linarith)

end Sigma2.UpperEntropyOperatorLimits
