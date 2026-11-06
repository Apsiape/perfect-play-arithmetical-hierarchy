import Sigma2.ProjectionLimits

noncomputable section
open scoped BigOperators
namespace Sigma2.TreeTail
open TreeFoundation

def step {P} (R : NormalRealization P) (T : Op) : Op :=
  ∑ a,R.creation a*T*star (R.creation a)

def tail {P} (R : NormalRealization P) : ℕ → Op
  | 0 => R.support
  | m+1 => step R (tail R m)

theorem step_supported {P} (R : NormalRealization P) (T : Op) :
    R.support*step R T=step R T ∧ step R T*R.support=step R T := by
  have ha (a : Fin 4) : star (R.creation a)*R.support=star (R.creation a) := by
    have hh := congrArg star (R.creation_supported a).1
    simpa only [star_mul,R.support_projection.1] using hh
  constructor
  · unfold step
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [← mul_assoc,← mul_assoc,(R.creation_supported a).1]
  · unfold step
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_assoc,ha]

theorem step_star {P} (R : NormalRealization P) (T : Op) (hT : star T=T) :
    star (step R T)=step R T := by
  unfold step
  rw [CompilerAlgebra.op_star_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [star_mul,star_mul,star_star,hT]
  noncomm_ring

theorem step_mul {P} (R : NormalRealization P) (Q T : Op) (hQ : Q*R.support=Q) :
    step R Q*step R T=step R (Q*T) := by
  classical
  unfold step
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = ∑ b,R.creation a*Q*(star (R.creation a)*R.creation b)*T*star (R.creation b) := by
      apply Finset.sum_congr rfl
      intro b _
      noncomm_ring
    _ = R.creation a*(Q*T)*star (R.creation a) := by
      rw [Finset.sum_eq_single a]
      · rw [R.isometries a a,if_pos rfl]
        calc
          _ = R.creation a*(Q*R.support)*T*star (R.creation a) := by noncomm_ring
          _ = _ := by rw [hQ]; noncomm_ring
      · intro b _ hba
        simp only [R.isometries a b,if_neg (Ne.symm hba),mul_zero,zero_mul]
      · simp

theorem tail_supported {P} (R : NormalRealization P) (m : ℕ) :
    R.support*tail R m=tail R m ∧ tail R m*R.support=tail R m := by
  cases m with
  | zero => exact ⟨R.support_projection.2,R.support_projection.2⟩
  | succ m => exact step_supported R _

theorem tail_projection {P} (R : NormalRealization P) (m : ℕ) :
    Projection (tail R m) := by
  induction m with
  | zero => exact R.support_projection
  | succ m ih =>
    refine ⟨step_star R _ ih.1,?_⟩
    change step R (tail R m)*step R (tail R m)=step R (tail R m)
    rw [step_mul R _ _ (tail_supported R m).2,ih.2]

theorem tail_next {P} (R : NormalRealization P) (m : ℕ) :
    tail R m*tail R (m+1)=tail R (m+1) := by
  induction m with
  | zero => exact (tail_supported R 1).1
  | succ m ih =>
    change step R (tail R m)*step R (tail R (m+1))=step R (tail R (m+1))
    rw [step_mul R _ _ (tail_supported R m).2,ih]

theorem tail_decreasing {P} (R : NormalRealization P) (m n : ℕ) (hmn : m≤n) :
    tail R m*tail R n=tail R n := by
  induction n,hmn using Nat.le_induction with
  | base => exact (tail_projection R m).2
  | succ n hmn ih =>
    calc
      _ = tail R m*(tail R n*tail R (n+1)) := by rw [tail_next]
      _ = (tail R m*tail R n)*tail R (n+1) := by noncomm_ring
      _ = _ := by rw [ih,tail_next]

theorem norm_step {P} (R : NormalRealization P) (T : Op) :
    ‖step R T‖ ≤ 4*‖T‖ := by
  have hh (a : Fin 4) : ‖R.creation a*T*star (R.creation a)‖ ≤ ‖T‖ := by
    calc
      _ ≤ (‖R.creation a‖*‖T‖)*‖(star (R.creation a) : Op)‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1*‖T‖)*1 := by
        rw [norm_star (R.creation a)]
        gcongr <;> exact creation_norm_le R a
      _ = _ := by ring
  calc
    _ ≤ ∑ a, ‖R.creation a*T*star (R.creation a)‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin 4, ‖T‖ := Finset.sum_le_sum (fun a _ => hh a)
    _ = _ := by simp

theorem density_step {P} (R : NormalRealization P) (T : Op) :
    R.density.op*step R T=(1/16:ℂ) • step R (R.density.op*T) := by
  unfold step
  rw [Finset.mul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← mul_assoc,← mul_assoc,R.modular a,smul_mul_assoc,smul_mul_assoc]
  congr 1

theorem density_tail_norm {P} (R : NormalRealization P) (m : ℕ) :
    ‖R.density.op*tail R m‖ ≤ (1/4:ℝ)^m*‖R.density.op‖ := by
  induction m with
  | zero => simp only [tail,density_support_right,pow_zero,one_mul,le_refl]
  | succ m ih =>
    change ‖R.density.op*step R (tail R m)‖ ≤ _
    rw [density_step,norm_smul]
    have hn : ‖(1/16:ℂ)‖=(1/16:ℝ) := by norm_num
    rw [hn]
    calc
      _ ≤ (1/16:ℝ)*(4*‖R.density.op*tail R m‖) := by gcongr; exact norm_step R _
      _ ≤ (1/16:ℝ)*(4*((1/4:ℝ)^m*‖R.density.op‖)) := by gcongr
      _ = _ := by rw [pow_succ]; ring

theorem density_tail_zero {P} (R : NormalRealization P) (v : H) :
    Filter.Tendsto (fun m => R.density.op (tail R m v)) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hg : Filter.Tendsto (fun m => (1/4:ℝ)^m*(‖R.density.op‖*‖v‖))
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0≤(1/4:ℝ)) (by norm_num)).mul_const
        (‖R.density.op‖*‖v‖)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hg
  intro m
  calc
    _ ≤ ‖R.density.op*tail R m‖*‖v‖ := (R.density.op*tail R m).le_opNorm v
    _ ≤ ((1/4:ℝ)^m*‖R.density.op‖)*‖v‖ := by gcongr; exact density_tail_norm R m
    _ = _ := by ring

theorem strong_tail_zero {P} (R : NormalRealization P) (v : H) :
    Filter.Tendsto (fun m => tail R m v) Filter.atTop (nhds 0) := by
  exact ProjectionLimits.strong_zero R (tail R) (tail_projection R)
    (fun m => (tail_supported R m).1) (tail_decreasing R) (density_tail_zero R) v

#print axioms strong_tail_zero
end Sigma2.TreeTail