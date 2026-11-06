import Sigma2.CompilerHonestDensity

/-! Exact squared-residual trace factors for the seventeen-corner lift. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerApproxBlocks
open FiniteAncilla FiniteSum CompilerHonestDensity
variable (d : ℕ) [NeZero d]

def singleBlocks (a b : Fin d) (A : Op) : Matrix (Fin d) (Fin d) Op :=
  fun i j => if i=a ∧ j=b then A else 0

theorem single_star (a b : Fin d) (A : Op) :
    star (singleBlocks d a b A)=singleBlocks d b a (star A) := by
  apply Matrix.ext
  intro i j
  by_cases hi : i=b <;> by_cases hj : j=a <;>
    simp [singleBlocks,Matrix.star_apply,hi,hj,star_zero Op]

theorem single_mul (a b c z : Fin d) (A B : Op) :
    singleBlocks d a b A*singleBlocks d c z B=
      if b=c then singleBlocks d a z (A*B) else 0 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply,Finset.sum_eq_single b]
  · by_cases hi : i=a <;> by_cases hj : j=z <;> by_cases hb : b=c <;>
      simp [singleBlocks,hi,hj,hb,Matrix.zero_apply]
  · intro k hk hkb
    have hz : singleBlocks d a b A i k=0 := by simp [singleBlocks,hkb]
    rw [hz,zero_mul]
  · simp

theorem diagonal_single (w : Fin d → ℝ) (A B : Op) (a b : Fin d) :
    diagonalBlocks d w A*singleBlocks d a b B=
      singleBlocks d a b ((w a:ℂ) • (A*B)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply,Finset.sum_eq_single a]
  · by_cases hi : i=a <;> by_cases hj : j=b <;>
      simp [diagonalBlocks,singleBlocks,hi,hj,smul_mul_assoc]
  · intro k hk hka
    have hz : singleBlocks d a b B k j=0 := by simp [singleBlocks,hka]
    rw [hz,mul_zero]
  · simp

@[simp] theorem matrix_entry (M : Matrix (Fin d) (Fin d) Op)
    (a b : Fin d) (i j : ℕ) :
    entry (matrixOp d M) (coordinates d (a,i)) (coordinates d (b,j))=entry (M a b) i j := by
  change fiber (coordinates d) (matrixOp d M (basis (coordinates d (b,j)))) a i=_
  rw [fiber_matrixOp]
  simp only [fiber_basis,apply_ite,map_zero]
  rw [Finset.sum_eq_single b]
  · rw [if_pos rfl]
    rfl
  · intro k hk hkb
    rw [if_neg hkb]
  · simp

theorem single_trace (b : Fin d) (A : Op) (hs : Summable (fun i => entry A i i)) :
    trace (matrixOp d (singleBlocks d b b A))=trace A := by
  have hnorm : Summable (fun p : Fin d × ℕ => ‖if p.1=b then entry A p.2 p.2 else 0‖) := by
    apply (summable_prod_of_nonneg (fun p => norm_nonneg _)).mpr
    refine ⟨?_,(hasSum_fintype _).summable⟩
    intro a
    by_cases hab : a=b
    · simpa only [hab,ite_true] using hs.norm
    · simp [hab]
  have hsum : Summable (fun p : Fin d × ℕ => if p.1=b then entry A p.2 p.2 else 0) :=
    hnorm.of_norm
  unfold trace
  rw [← (coordinates d).tsum_eq]
  have he (p : Fin d × ℕ) :
      entry (matrixOp d (singleBlocks d b b A)) (coordinates d p) (coordinates d p)=
        if p.1=b then entry A p.2 p.2 else 0 := by
    rcases p with ⟨a,i⟩
    rw [matrix_entry]
    by_cases hab : a=b <;> simp [singleBlocks,hab,entry]
  simp_rw [he]
  rw [hsum.tsum_prod,tsum_fintype,Finset.sum_eq_single b]
  · simp
  · intro a ha hab
    simp [hab]
  · simp

/-- The squared norm of a rectangular lift is weighted by its input corner.
There is no density-gap assumption and no approximate extraction. -/
theorem single_residual_energy (w : Fin d → ℝ) (h : Density) (a b : Fin d) (A : Op) :
    trace (weightedOp d w h.op*
      (star (matrixOp d (singleBlocks d a b A))*matrixOp d (singleBlocks d a b A)))=
      (w b:ℂ)*trace (h.op*(star A*A)) := by
  rw [← matrixOp_star,← matrixOp_mul,single_star,single_mul,if_pos rfl,
    weightedOp,← matrixOp_mul,diagonal_single]
  have hpos : Positive (star A*A) := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have hs := (FockTrace.density_diagonal h (star A*A) hpos).mul_left (w b:ℂ)
  have hss : Summable (fun i => entry ((w b:ℂ) • (h.op*(star A*A))) i i) := hs
  rw [single_trace d b _ hss]
  exact CompilerAlgebra.trace_smul _ _

/-- In the scaffold, all source-column squared residuals have factor 1/121. -/
theorem source_residual_energy (h : Density) (a : Fin 17) (A : Op) :
    (trace ((scaffoldDensity h).op*
      (star (matrixOp 17 (singleBlocks 17 a 0 A))*matrixOp 17 (singleBlocks 17 a 0 A)))).re=
      (1/121:ℝ)*(trace (h.op*(star A*A))).re := by
  change (trace (weightedOp 17 (fun i => (CompilerScaffold.cornerWeight i:ℝ)) h.op*_)).re=_
  rw [single_residual_energy]
  norm_num [CompilerScaffold.cornerWeight,Complex.mul_re]

/-- The range residual is in selected corner e4=corner 13 and has factor 16/121. -/
theorem range_residual_energy (h : Density) (A : Op) :
    (trace ((scaffoldDensity h).op*
      (star (matrixOp 17 (singleBlocks 17 13 13 A))*matrixOp 17 (singleBlocks 17 13 13 A)))).re=
      (16/121:ℝ)*(trace (h.op*(star A*A))).re := by
  change (trace (weightedOp 17 (fun i => (CompilerScaffold.cornerWeight i:ℝ)) h.op*_)).re=_
  rw [single_residual_energy]
  norm_num [CompilerScaffold.cornerWeight,Complex.mul_re]

#print axioms single_residual_energy
#print axioms source_residual_energy
#print axioms range_residual_energy
end Sigma2.CompilerApproxBlocks
