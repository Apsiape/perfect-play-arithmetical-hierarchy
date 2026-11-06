import Sigma2.CompilerApproxBlocks
import Sigma2.CompilerHonestQutrit

/-! The exact qutrit factor in the honest compiler's squared row residual. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerApproxQutrit
open FiniteAncilla FiniteSum CompilerHonestDensity CompilerApproxBlocks
open TraceProducts Coefficients FockTrace

/-- Cyclic transport for an arbitrary bounded operator and a normal density,
proved using absolutely summable covariance columns. -/
theorem trace_transport (h : Density) (A : Op) :
    trace (A*h.op*star A)=trace (h.op*(star A*A)) := by
  let u := rootFamily h
  have hu := root_summable h
  have hB : Positive (star A*A) := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have h1 := covariance_mul_trace (fun i => A (u i)) (image_summable A u hu)
    1 ContinuousLinearMap.isPositive_one
  have h2 := covariance_mul_trace u hu (star A*A) hB
  have hi (i : ℕ) : inner ℂ (A (u i)) (A (u i))=
      inner ℂ ((star A*A) (u i)) (u i) := by
    calc
      _=inner ℂ (u i) ((star A*A) (u i)) := (A.adjoint_inner_right _ _).symm
      _=_ := (hB.isSymmetric _ _).symm
  calc
    _=trace (covariance (fun i => A (u i))) := by
      rw [density_eq_covariance,covariance_map _ (root_summable _) A]
    _=∑' i,inner ℂ (A (u i)) (A (u i)) := by
      simpa only [mul_one,one_apply_eq_self] using h1.2.1
    _=∑' i,inner ℂ ((star A*A) (u i)) (u i) := tsum_congr hi
    _=trace (h.op*(star A*A)) := by
      rw [density_eq_covariance]
      exact h2.2.1.symm

theorem centralizer_square_trace (h : Density) (A : Op) (hc : Centralizes h.op A) :
    trace (h.op*(A*star A))=trace (h.op*(star A*A)) := by
  have hcs : star A*h.op=h.op*star A := by
    have hh := congrArg (fun B : Op => star B) hc
    simpa only [star_mul,h.positive.isSelfAdjoint.star_eq] using hh
  calc
    _=trace (star A*h.op*A) := by simpa only [star_star] using (trace_transport h (star A)).symm
    _=_ := by rw [hcs,mul_assoc]

theorem weighted_single_trace {d : ℕ} [NeZero d] (w : Fin d → ℝ)
    (h : Density) (b : Fin d) (B : Op) (hB : Positive B) :
    trace (weightedOp d w h.op*matrixOp d (singleBlocks d b b B))=
      (w b:ℂ)*trace (h.op*B) := by
  rw [weightedOp,← matrixOp_mul,diagonal_single]
  have hs := (density_diagonal h B hB).mul_left (w b:ℂ)
  have hss : Summable (fun i => entry ((w b:ℂ) • (h.op*B)) i i) := hs
  rw [single_trace d b _ hss]
  exact CompilerAlgebra.trace_smul _ _

theorem single_positive {d : ℕ} [NeZero d] (b : Fin d) (B : Op) (hB : Positive B) :
    Positive (matrixOp d (singleBlocks d b b B)) := by
  have he : singleBlocks d b b B=diagonalBlocks d (fun i => if i=b then 1 else 0) B := by
    apply Matrix.ext
    intro i j
    by_cases hi : i=b <;> by_cases hj : j=b <;> by_cases hij : i=j <;>
      simp [singleBlocks,diagonalBlocks,hi,hj,hij] <;> aesop
  rw [he]
  exact weighted_positive d _ (fun i => by split_ifs <;> norm_num) B hB

theorem trace_density_add (h : Density) (B C : Op) (hB : Positive B) (hC : Positive C) :
    trace (h.op*(B+C))=trace (h.op*B)+trace (h.op*C) := by
  have ht := trace_density_sum h Finset.univ (fun i : Fin 2 => if i=0 then B else C)
    (fun i _ => by split_ifs <;> assumption)
  simpa only [Fin.sum_univ_two,ite_true,show (1:Fin 2)≠0 by decide,ite_false] using ht

def residualBlocks (A : Op) : Matrix (Fin 3) (Fin 3) Op :=
  singleBlocks 3 0 1 A+singleBlocks 3 1 0 (star A)

theorem residual_square (A : Op) :
    star (residualBlocks A)*residualBlocks A=
      singleBlocks 3 0 0 (A*star A)+singleBlocks 3 1 1 (star A*A) := by
  rw [residualBlocks,star_add (singleBlocks 3 0 1 A) (singleBlocks 3 1 0 (star A)),
    add_mul,mul_add,mul_add,single_star,single_star,star_star]
  norm_num [single_mul]
  abel

/-- Tensoring with the scalar qutrit costs exactly 2/3 in squared row energy. -/
theorem qutrit_residual_energy (h : Density) (A : Op) (hc : Centralizes h.op A) :
    let qh := weightedDensity 3 (fun _ => (1/3:ℝ)) (fun _ => by norm_num)
      (by norm_num [Fin.sum_univ_three]) h
    (trace (qh.op*(star (matrixOp 3 (residualBlocks A))*matrixOp 3 (residualBlocks A)))).re=
      (2/3:ℝ)*(trace (h.op*(star A*A))).re := by
  dsimp only
  rw [← matrixOp_star,← matrixOp_mul,residual_square,matrixOp_add]
  have hAA : Positive (A*star A) := by
    have hh := ContinuousLinearMap.isPositive_adjoint_comp_self (star A)
    change Positive (star (star A)*star A) at hh
    rw [star_star] at hh
    exact hh
  have hAsA : Positive (star A*A) := ContinuousLinearMap.isPositive_adjoint_comp_self A
  rw [trace_density_add _ _ _ (single_positive _ _ hAA) (single_positive _ _ hAsA)]
  change (trace (weightedOp 3 (fun _ => (1/3:ℝ)) h.op*matrixOp 3 (singleBlocks 3 0 0 (A*star A)))+
    trace (weightedOp 3 (fun _ => (1/3:ℝ)) h.op*matrixOp 3 (singleBlocks 3 1 1 (star A*A)))).re=_
  rw [weighted_single_trace _ _ _ _ hAA,weighted_single_trace _ _ _ _ hAsA,
    centralizer_square_trace h A hc]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  ring

#print axioms trace_transport
#print axioms centralizer_square_trace
#print axioms qutrit_residual_energy
end Sigma2.CompilerApproxQutrit
