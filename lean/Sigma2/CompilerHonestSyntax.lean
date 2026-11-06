import Sigma2.CompilerHonestLabels
import Sigma2.CompilerScaffoldAlgebra

/-! The new operator encodings agree with the actual frozen polynomial syntax. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerHonestSyntax
open CompilerScaffold CompilerHonestLabels

theorem eval_one (U : ℕ → Op) : evalPoly U one=1 := by
  simp [evalPoly,one,evalWord]

theorem eval_scalar (U : ℕ → Op) (q : ℚ) : evalPoly U (scalar q)=(q:ℂ) • (1:Op) := by
  simp [evalPoly,scalar,evalWord]

theorem eval_atom (U : ℕ → Op) (i : ℕ) : evalPoly U (atom i)=U i := by
  simp [evalPoly,atom,evalWord]

theorem eval_adj (U : ℕ → Op) (p : Poly) : evalPoly U (adj p)=star (evalPoly U p) := by
  induction p with
  | nil =>
      change (0:Op)=star (0:Op)
      exact (star_zero Op).symm
  | cons t p ih =>
      change (t.1:ℂ) • evalWord U (adjWord t.2)+evalPoly U (adj p)=
        star ((t.1:ℂ) • evalWord U t.2+evalPoly U p)
      rw [evalWord_adj,ih,star_add ((t.1:ℂ) • evalWord U t.2) (evalPoly U p),
        star_smul,star_ratCast]

theorem eval_corner (U : ℕ → Op) (i : ℕ) :
    evalPoly U (corner i)=(1/2:ℂ) • (1+U i) := by
  rw [corner,evalPoly_scale,evalPoly_append,eval_one,eval_atom]
  norm_num

/-- The honest operator decoder is exactly `labelCopy`, including its positive
and contraction coefficients, at the frozen numeric allocation. -/
theorem eval_labelCopy (P : Presentation) (U : ℕ → Op) (r i : ℕ) :
    evalPoly U (labelCopy P r i)=
      decodeEncoding (evalPoly U (e r))
        (U (33+r*encodingCount P+encodingOffset P i))
        (U (33+r*encodingCount P+(encodingOffset P i+1)))
        ((P.types[i]?).getD .unitary) := by
  cases ht : (P.types[i]?).getD .unitary <;>
    simp only [labelCopy,ht,evalPoly_mul,copyAtom,eval_atom,evalPoly_scale,
      evalPoly_append,eval_one,eval_scalar,eval_adj,decodeEncoding] <;> norm_num

#print axioms eval_labelCopy
end Sigma2.CompilerHonestSyntax
