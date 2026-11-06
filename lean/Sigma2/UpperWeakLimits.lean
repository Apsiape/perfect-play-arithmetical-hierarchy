import Sigma2.UpperCompact
import Sigma2.UpperAnalytic

noncomputable section
open scoped BigOperators InnerProductSpace
open Filter
namespace Sigma2.UpperWeakLimits

def Converges (T : ℕ → Op) (L : Op) : Prop :=
  ∀ u v : H,Tendsto (fun n => inner ℂ u (T n v)) atTop (nhds (inner ℂ u (L v)))

theorem positive (T : ℕ → Op) (L : Op) (h : Converges T L)
    (hp : ∀ n,Positive (T n)) : Positive L := by
  constructor
  · intro u v
    have hl : Tendsto (fun n => inner ℂ (T n u) v) atTop (nhds (inner ℂ (L u) v)) := by
      simpa only [RCLike.star_def,inner_conj_symm] using (h v u).star
    have hr : Tendsto (fun n => inner ℂ (T n u) v) atTop (nhds (inner ℂ u (L v))) := by
      convert h u v using 1
      funext n
      exact (hp n).isSymmetric u v
    exact tendsto_nhds_unique hl hr
  · intro v
    have hh : 0≤(inner ℂ v (L v)).re := ge_of_tendsto
      ((Complex.continuous_re.tendsto _).comp (h v v))
      (Eventually.of_forall (fun n => (hp n).re_inner_nonneg_right v))
    simpa only [ContinuousLinearMap.reApplyInnerSelf_apply,inner_re_symm,RCLike.re_eq_complex_re] using hh

theorem sum_eq_one {ι : Type} [Fintype ι] (T : ι → ℕ → Op) (L : ι → Op)
    (h : ∀ i,Converges (T i) (L i)) (hs : ∀ n,∑ i,T i n=1) : ∑ i,L i=1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro u
  have ht := tendsto_finsetSum Finset.univ (fun i _ => h i u v)
  have he n : (∑ i,inner ℂ u (T i n v))=inner ℂ u v := by
    rw [← inner_sum,← sum_apply,hs n]
    rfl
  simp_rw [he] at ht
  have hh := tendsto_nhds_unique ht tendsto_const_nhds
  simpa only [sum_apply,inner_sum,one_apply_eq_self] using hh

theorem entry (T : ℕ → Op) (L : Op) (h : Converges T L) (i j : ℕ) :
    Tendsto (fun n => Sigma2.entry (T n) i j) atTop (nhds (Sigma2.entry L i j)) := by
  simpa only [basis,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,Sigma2.entry]
    using h (basis i) (basis j)

/-- Uniform operator bounds survive weak limits. -/
theorem norm_le (T : ℕ → Op) (L : Op) (h : Converges T L) (C : ℝ) (hC : 0≤C)
    (hb : ∀ n,‖T n‖≤C) : ‖L‖≤C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have hbound : ‖L v‖^2 ≤ ‖L v‖ * (C*‖v‖) := by
    have hh := le_of_tendsto (h (L v) v).norm (Eventually.of_forall fun n =>
      (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg v))) (norm_nonneg (L v))))
    simpa only [inner_self_eq_norm_sq_to_K,norm_pow,RCLike.norm_ofReal,abs_norm] using hh
  by_cases hz : ‖L v‖=0
  · rw [hz]
    positivity
  · nlinarith [norm_pos_iff.mpr (norm_ne_zero_iff.mp hz)]

/-- Entry bounds tending to zero force a weak operator limit to vanish. -/
theorem zero_of_stage_bounds (T : ℕ → Op) (L : Op) (h : Converges T L)
    (κ : ℝ) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hb : ∀ n i j,‖Sigma2.entry (T n) i j‖^2 ≤ κ/(φ n+2:ℝ)) : L=0 := by
  have hnat : Tendsto (fun n => (φ n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop
  have hden : Tendsto (fun n => (φ n:ℝ)+2) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) hnat
  have hz : Tendsto (fun n => κ/(φ n+2:ℝ)) atTop (nhds 0) := hden.const_div_atTop κ
  apply UpperAnalytic.entry_ext
  intro i j
  have hh := le_of_tendsto_of_tendsto ((entry T L h i j).norm.pow 2) hz
    (Eventually.of_forall fun n => hb n i j)
  have he : Sigma2.entry L i j=0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hh (sq_nonneg _)))
  exact he

end Sigma2.UpperWeakLimits
