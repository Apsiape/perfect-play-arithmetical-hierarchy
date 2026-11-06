import Sigma2.CompilerHonestRefinements
import Sigma2.CompilerHonestDensityEntropy

/-! Finite entropy of both genuine marginals of the honest strategy. Bob's
 marginal is the actual coordinate-transposed density. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerHonestMarginalEntropy
open Compiler CompilerHonestState CompilerHonestFMSLift CompilerHonestRefinements
  CompilerHonestDensityEntropy CoefficientOperator

theorem inner_star (u v : H) : inner ℂ (star u) (star v)=star (inner ℂ u v) := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum,tsum_star]
  apply tsum_congr
  intro i
  simp [lp.star_apply,RCLike.inner_apply,star_mul,mul_comm]

theorem orthonormal_star (u : ℕ → H) (hu : Orthonormal ℂ u) :
    Orthonormal ℂ (fun i => star (u i)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_star,orthonormal_iff_ite.mp hu]
  split_ifs <;> simp

/-- Coordinate conjugation preserves the same complete eigenvalue list. -/
theorem transposed_finite_entropy (h : Density) (hh : FiniteDensityEntropy h) :
    FiniteDensityEntropy (transposedDensity h) := by
  obtain ⟨p,u,hp0,hp,hp1,hu,he,hent⟩ := hh
  refine ⟨p,fun i => star (u i),hp0,hp,hp1,orthonormal_star u hu,?_,hent⟩
  intro v
  change star (star h.op (star v))=_
  rw [h.positive.isSelfAdjoint.star_eq,he,tsum_star]
  apply tsum_congr
  intro i
  rw [star_smul,star_mul]
  have hc : star (inner ℂ (u i) (star v))=inner ℂ (star (u i)) v := by
    rw [← inner_star,star_star]
  rw [hc]
  simp [mul_comm]

theorem density_finite_entropy (h : Density) (hh : FiniteDensityEntropy h) :
    FiniteDensityEntropy (density h) :=
  weighted_finite_entropy 3 _ _ _ _ (scaffold_finite_entropy h hh)

/-- The fully specified realization-only base strategy has finite entropy on
 Alice's and Bob's actual marginals whenever the input density does. -/
theorem strategy_finite_entropy {P : Presentation} (R : StructuralRealization P)
    (hh : FiniteDensityEntropy R.density) : FiniteMarginalEntropy (strategy R) := by
  have he := density_finite_entropy R.density hh
  exact ⟨density R.density,transposedDensity (density R.density),
    CompilerHonestState.marginalA _ _,CompilerHonestState.marginalB _ _,
    he,transposed_finite_entropy _ he⟩

#print axioms transposed_finite_entropy
#print axioms strategy_finite_entropy
end Sigma2.CompilerHonestMarginalEntropy
