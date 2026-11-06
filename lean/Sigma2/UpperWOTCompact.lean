import Sigma2.UpperWeakLimits
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Topology.MetricSpace.Equicontinuity

noncomputable section
open scoped BigOperators InnerProductSpace
open Filter
namespace Sigma2.UpperWOTCompact

/-- A functional on the fixed Hilbert model is determined by its basis values. -/
theorem dual_ext_basis (f g : StrongDual ℂ H) (h : ∀ i,f (basis i)=g (basis i)) : f=g := by
  apply ContinuousLinearMap.ext
  intro v
  have he (i : ℕ) : f (lp.single 2 i (v i))=g (lp.single 2 i (v i)) := by
    have hs : lp.single 2 i (v i)=v i • basis i := by
      simp only [basis,← lp.single_smul,smul_eq_mul,mul_one]
    simp only [hs,map_smul,h]
  have hf := (lp.hasSum_single (by norm_num : (2:ENNReal)≠⊤) v).mapL f
  have hg := (lp.hasSum_single (by norm_num : (2:ENNReal)≠⊤) v).mapL g
  simp only [he] at hf
  exact hf.unique hg

/-- Weak-* compact ball of row functionals. -/
abbrev RowBall := {f : WeakDual ℂ H // f.toStrongDual ∈ Metric.closedBall 0 1}

instance : CompactSpace RowBall :=
  isCompact_iff_compactSpace.mp (WeakDual.isCompact_closedBall (0 : StrongDual ℂ H) 1)

instance : TopologicalSpace.MetrizableSpace RowBall := by
  apply Metric.PiNatEmbed.TopologicalSpace.MetrizableSpace.of_countable_separating
    (fun i : ℕ => fun f : RowBall => f.val (basis i))
    (fun i => (WeakDual.eval_continuous (basis i)).comp continuous_subtype_val)
  intro f g hfg
  by_contra hn
  apply hfg
  apply Subtype.ext
  apply WeakDual.toStrongDual.injective
  apply dual_ext_basis
  intro i
  exact not_ne_iff.mp (fun hi => hn ⟨i,hi⟩)

/-- Coordinate convergence of uniformly bounded operators implies WOT convergence. -/
theorem converges_of_coordinates (T : ℕ → Op) (L : Op) (C : ℝ)
    (hb : ∀ n,‖T n‖≤C)
    (he : ∀ i v,Tendsto (fun n => (T n v) i) atTop (nhds (L v i))) :
    UpperWeakLimits.Converges T L := by
  intro u v
  have heq : Equicontinuous (fun n => fun w : H => inner ℂ w (T n v)) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r => (C*‖v‖)*r)
      (by simpa using ((tendsto_id : Tendsto (fun r : ℝ => r) (nhds 0) (nhds 0)).const_mul (C*‖v‖)))
    intro w z n
    rw [dist_eq_norm,← inner_sub_left]
    calc
      ‖inner ℂ (w-z) (T n v)‖ ≤ ‖w-z‖*‖T n v‖ := norm_inner_le_norm _ _
      _ ≤ ‖w-z‖*(C*‖v‖) := mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hb n) (norm_nonneg _))) (norm_nonneg _)
      _ = (C*‖v‖)*dist w z := by rw [dist_eq_norm]; ring
  have hc := heq.isClosed_setOfPred_tendsto (l := atTop)
    (show Continuous (fun w : H => inner ℂ w (L v)) by fun_prop)
  apply hc.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ENNReal)≠⊤) u)
  apply Eventually.of_forall
  intro s
  change Tendsto (fun n => inner ℂ (∑ i ∈ s,lp.single 2 i (u i)) (T n v)) atTop
    (nhds (inner ℂ (∑ i ∈ s,lp.single 2 i (u i)) (L v)))
  simp only [sum_inner,lp.inner_single_left,RCLike.inner_apply]
  exact tendsto_finsetSum s (fun i _ => (he i v).mul_const _)

/-- One common WOT subsequence for a countable family of contractions. -/
theorem exists_common_subsequence {ι : Type} [Countable ι]
    (T : ℕ → ι → Op) (hb : ∀ n a,‖T n a‖≤1) :
    ∃ (L : ι → Op) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ a,‖L a‖≤1) ∧
      ∀ a,UpperWeakLimits.Converges (fun n => T (φ n) a) (L a) := by
  let r (n : ℕ) (ai : ι × ℕ) : RowBall :=
    ⟨StrongDual.toWeakDual ((lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 ai.2).comp (T n ai.1)),by
      rw [Metric.mem_closedBall,dist_zero_right]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro v
      change ‖(T n ai.1 v) ai.2‖ ≤ 1*‖v‖
      exact (lp.norm_apply_le_norm (by norm_num : (2:ENNReal)≠0) _ _).trans
        ((ContinuousLinearMap.le_opNorm _ _).trans (by nlinarith [norm_nonneg v,hb n ai.1]))⟩
  obtain ⟨f,_,φ,hφ,hlim⟩ := (isCompact_univ : IsCompact (Set.univ : Set ((ι × ℕ) → RowBall))).tendsto_subseq
    (fun n => Set.mem_univ (r n))
  have hcoord (a : ι) (i : ℕ) (v : H) :
      Tendsto (fun n => T (φ n) a v i) atTop (nhds (f (a,i) |>.val v)) := by
    exact ((WeakDual.eval_continuous v).comp continuous_subtype_val).tendsto _ |>.comp
      (((continuous_apply (a,i)).tendsto _).comp hlim)
  have hsum (a : ι) (v : H) (s : Finset ℕ) :
      (∑ i ∈ s,‖(f (a,i)).val v‖^2)≤‖v‖^2 := by
    apply le_of_tendsto (tendsto_finsetSum s (fun i _ => (hcoord a i v).norm.pow 2))
    apply Eventually.of_forall
    intro n
    calc
      _ ≤ ‖T (φ n) a v‖^2 := (by simpa only [(Coefficients.norm_sq_hasSum _).tsum_eq] using (Coefficients.norm_sq_hasSum (T (φ n) a v)).summable.sum_le_tsum s (fun i _ => sq_nonneg _))
      _ ≤ ‖v‖^2 := pow_le_pow_left₀ (norm_nonneg _) ((ContinuousLinearMap.le_opNorm _ _).trans
        (by nlinarith [norm_nonneg v,hb (φ n) a])) 2
  let l (a : ι) (v : H) : H := ⟨fun i => (f (a,i)).val v,memℓp_gen (by
    simpa using (summable_of_sum_le (fun i => sq_nonneg _) (hsum a v)))⟩
  have hl (a : ι) (v : H) : ‖l a v‖≤‖v‖ := by
    apply lp.norm_le_of_forall_sum_le (by norm_num : 0<(2:ENNReal).toReal) (norm_nonneg v)
    simpa using hsum a v
  let L (a : ι) : Op := LinearMap.mkContinuous
    { toFun := l a
      map_add' := by intro v w; ext i; exact map_add (f (a,i)).val v w
      map_smul' := by intro c v; ext i; exact map_smul (f (a,i)).val c v }
    1 (by simpa using hl a)
  refine ⟨L,φ,hφ,(fun a => ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by change ‖l a v‖≤1*‖v‖; simpa using hl a v)),?_⟩
  intro a
  exact converges_of_coordinates _ _ 1 (fun n => hb (φ n) a) (hcoord a)

end Sigma2.UpperWOTCompact



