import Sigma2.FockModel

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal Classical
namespace Sigma2.FockModel
variable {ι : Type}

/-- The unitary induced by a permutation of the Hilbert coordinates. -/
def permutation (e : Equiv.Perm ι) : Operator ι :=
  (reindex e.symm : Space ι →L[ℂ] Space ι)

@[simp] lemma permutation_apply (e : Equiv.Perm ι) (v : Space ι) (i : ι) :
    permutation e v i=v (e.symm i) := rfl

lemma permutation_single (e : Equiv.Perm ι) (i : ι) :
    permutation e (lp.single 2 i 1)=lp.single 2 (e i) 1 := by
  ext j
  change (lp.single 2 i (1:ℂ) : Space ι) (e.symm j)=(lp.single 2 (e i) 1 : Space ι) j
  by_cases h : j=e i
  · subst j; simp
  · have hh : e.symm j≠i := fun hh => h (by simpa using congrArg e hh)
    simp [lp.single_apply,h,hh]

lemma permutation_star (e : Equiv.Perm ι) :
    star (permutation e)=permutation e.symm := by
  change ContinuousLinearMap.adjoint (reindex e.symm : Space ι →L[ℂ] Space ι)=_
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext v i
  rfl

lemma permutation_unitary (e : Equiv.Perm ι) :
    star (permutation e)*permutation e=1 ∧ permutation e*star (permutation e)=1 := by
  rw [permutation_star]
  constructor <;> ext v i <;> simp

lemma permutation_mul (e f : Equiv.Perm ι) :
    permutation e*permutation f=permutation (f.trans e) := by
  ext v i
  rfl

#print axioms permutation_unitary
end Sigma2.FockModel
