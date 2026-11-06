import Sigma2.CompilerScaffold
import Sigma2.FiniteAncillaDensity
import Sigma2.FiniteAncillaMatrix
import Sigma2.FockTrace

/-! Weighted finite scaffold densities in the fixed l2 coordinate model. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.CompilerHonestDensity
open FiniteAncilla FiniteSum
variable (d : ℕ) [NeZero d]

def diagonalBlocks (w : Fin d → ℝ) (A : Op) : Matrix (Fin d) (Fin d) Op :=
  fun a b => if a=b then (w a:ℂ) • A else 0

def weightedOp (w : Fin d → ℝ) (A : Op) : Op := matrixOp d (diagonalBlocks d w A)

@[simp] theorem weighted_fiber (w : Fin d → ℝ) (A : Op) (v : H) (a : Fin d) :
    fiber (coordinates d) (weightedOp d w A v) a=
      (w a:ℂ) • A (fiber (coordinates d) v a) := by
  rw [weightedOp,fiber_matrixOp]
  rw [Finset.sum_eq_single a]
  · rw [diagonalBlocks,if_pos rfl]
    rfl
  · intro b hb hba
    rw [diagonalBlocks,if_neg (Ne.symm hba)]
    rfl
  · simp

@[simp] theorem weighted_entry (w : Fin d → ℝ) (A : Op)
    (a b : Fin d) (i j : ℕ) :
    entry (weightedOp d w A) (coordinates d (a,i)) (coordinates d (b,j))=
      if a=b then (w a:ℂ)*entry A i j else 0 := by
  change fiber (coordinates d) (weightedOp d w A (basis (coordinates d (b,j)))) a i=_
  rw [weighted_fiber,fiber_basis]
  by_cases hab : a=b
  · subst b
    simp only [ite_true]
    rfl
  · simp [hab]

@[simp] theorem weighted_diagonal (w : Fin d → ℝ) (A : Op) (p : Fin d × ℕ) :
    (entry (weightedOp d w A) (coordinates d p) (coordinates d p)).re=
      w p.1*(entry A p.2 p.2).re := by
  rcases p with ⟨a,i⟩
  rw [weighted_entry,if_pos rfl]
  simp [Complex.mul_re]

theorem weighted_positive (w : Fin d → ℝ) (hw : ∀ a,0≤w a)
    (A : Op) (hA : Positive A) : Positive (weightedOp d w A) := by
  constructor
  · intro v z
    change inner ℂ (weightedOp d w A v) z=inner ℂ v (weightedOp d w A z)
    rw [inner_fibers (coordinates d),inner_fibers (coordinates d)]
    simp only [weighted_fiber,inner_smul_left,inner_smul_right,Complex.star_def,
      Complex.conj_ofReal]
    exact Finset.sum_congr rfl (fun a _ => congrArg (fun c : ℂ => (w a:ℂ)*c)
      (hA.isSymmetric _ _))
  · intro v
    change 0≤(inner ℂ (weightedOp d w A v) v).re
    rw [inner_fibers (coordinates d)]
    simp only [weighted_fiber,inner_smul_left,Complex.star_def,Complex.conj_ofReal,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) (hA.re_inner_nonneg_left _))

theorem weighted_diagonal_summable (w : Fin d → ℝ) (hw : ∀ a,0≤w a) (h : Density) :
    Summable (fun p : Fin d × ℕ => w p.1*(entry h.op p.2 p.2).re) := by
  apply (summable_prod_of_nonneg (fun p => ?_)).mpr
  · exact ⟨fun a => by simpa using h.diagonal_summable.mul_left (w a),(hasSum_fintype _).summable⟩
  · apply mul_nonneg (hw _)
    simpa [basis,entry,lp.inner_single_left] using h.positive.re_inner_nonneg_right (basis p.2)

/-- An arbitrary positive finite probability law weights copies of one density. -/
def weightedDensity (w : Fin d → ℝ) (hw : ∀ a,0≤w a) (hs : ∑ a,w a=1)
    (h : Density) : Density where
  op := weightedOp d w h.op
  positive := weighted_positive d w hw h.op h.positive
  diagonal_summable := by
    apply (coordinates d).summable_iff.mp
    change Summable (fun p : Fin d × ℕ =>
      (entry (weightedOp d w h.op) (coordinates d p) (coordinates d p)).re)
    simp only [weighted_diagonal]
    exact weighted_diagonal_summable d w hw h
  trace_one := by
    rw [← (coordinates d).tsum_eq]
    change (∑' p : Fin d × ℕ,
      (entry (weightedOp d w h.op) (coordinates d p) (coordinates d p)).re)=1
    simp only [weighted_diagonal]
    rw [(weighted_diagonal_summable d w hw h).tsum_prod,tsum_fintype]
    simpa only [tsum_mul_left,h.trace_one,mul_one] using hs

/-- Strictly positive scalar weights preserve the exact state support and
faithfulness there, even if that support has a nontrivial ambient kernel. -/
theorem weighted_support (w : Fin d → ℝ) (hw : ∀ a,0<w a) (hs : ∑ a,w a=1)
    (h : Density) (e : Op) (he : Preliminaries.SupportOf h e) :
    Preliminaries.SupportOf (weightedDensity d w (fun a => (hw a).le) hs h) (amplify d e) := by
  have hp : Projection (amplify d e) := by
    constructor
    · rw [← amplify_star,he.1.1]
    · rw [← amplify_mul,he.1.2]
  refine ⟨hp,?_,?_⟩
  · ext v : 1
    apply ext_fiber (coordinates d)
    intro a
    change fiber (coordinates d) (amplify d e (weightedOp d w h.op v)) a=
      fiber (coordinates d) (weightedOp d w h.op v) a
    rw [fiber_amplify,weighted_fiber,map_smul,← mul_apply_eq_comp,he.2.1]
  · intro v hv hz
    apply ext_fiber (coordinates d)
    intro a
    have hve := congrArg (fun z : H => fiber (coordinates d) z a) hv
    have hvz := congrArg (fun z : H => fiber (coordinates d) z a) hz
    rw [fiber_amplify] at hve
    change fiber (coordinates d) (weightedOp d w h.op v) a=fiber (coordinates d) 0 a at hvz
    rw [weighted_fiber,fiber_zero] at hvz
    have hwa : (w a:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hw a).ne'
    have hez : h.op (fiber (coordinates d) v a)=0 := (smul_eq_zero.mp hvz).resolve_left hwa
    rw [fiber_zero]
    exact he.2.2 _ hve hez

/-- The exact seventeen-corner probability law used by the frozen compiler. -/
def scaffoldDensity (h : Density) : Density :=
  weightedDensity 17 (fun i => (CompilerScaffold.cornerWeight i:ℝ))
    (fun i => by exact_mod_cast (CompilerScaffold.cornerWeight_positive i).le)
    (by exact_mod_cast CompilerScaffold.cornerWeight_sum) h

theorem scaffold_support (h : Density) (e : Op) (he : Preliminaries.SupportOf h e) :
    Preliminaries.SupportOf (scaffoldDensity h) (amplify 17 e) := by
  exact weighted_support 17 _
    (fun i => by exact_mod_cast CompilerScaffold.cornerWeight_positive i)
    (by exact_mod_cast CompilerScaffold.cornerWeight_sum) h e he

#print axioms weightedDensity
#print axioms weighted_support
#print axioms scaffold_support
end Sigma2.CompilerHonestDensity
