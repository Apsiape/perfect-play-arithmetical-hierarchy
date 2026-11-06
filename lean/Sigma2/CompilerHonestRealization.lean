import Sigma2.TreeFoundation
import Sigma2.CompilerScaffold

/-! The exact realization is the zero-residual special case of the honest
structural construction. This module does not assume an honest compiler theorem. -/
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestRealization
open Compiler

/-- Exact realizations satisfy all frozen structural hypotheses, including the
creation norm bound, which follows from their isometry equations. -/
def structural {P : Presentation} (R : NormalRealization P) : StructuralRealization P where
  support := R.support
  support_projection := R.support_projection
  density := R.density
  density_supported := R.density_supported
  faithful_on := R.faithful_on
  label := R.label
  creation := R.creation
  label_supported := R.label_supported
  creation_supported := R.creation_supported
  typed := R.typed
  creation_contractive := TreeFoundation.creation_norm_le R
  centralizer := R.centralizer
  modular := R.modular

/-- Every application residual, in the actual frozen list, vanishes exactly. -/
theorem application_residual_zero {P : Presentation} (R : NormalRealization P)
    (r : Op) (hr : r ∈ applicationResiduals P (structural R)) : r=0 := by
  simp only [applicationResiduals,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with (((((hr|hr)|hr)|hr)|hr)|hr)
  · rcases List.mem_flatMap.mp hr with ⟨a,ha,hb⟩
    rcases List.mem_ofFn.mp hb with ⟨b,hb⟩
    rw [← hb]
    change star (R.creation a)*R.creation b-(if a=b then R.support else 0)=0
    rw [R.isometries,sub_self]
  · rcases hr with rfl
    change ((∑ a,R.creation a*star (R.creation a))-(R.support-R.label P.root))=0
    rw [R.ranges,sub_self]
  · rcases List.mem_map.mp hr with ⟨p,hp,he⟩
    rw [← he]
    exact R.central_equations p hp
  · rcases List.mem_map.mp hr with ⟨p,hp,he⟩
    rw [← he]
    exact sub_eq_zero.mpr (R.endpoint_equations p hp)
  · rcases List.mem_map.mp hr with ⟨p,hp,he⟩
    rw [← he]
    exact R.zero_equations p hp
  · rcases List.mem_map.mp hr with ⟨row,hrow,he⟩
    rw [← he]
    exact R.linear_equations row hrow

theorem residual_energy_zero {P : Presentation} (R : NormalRealization P) :
    ((applicationResiduals P (structural R)).map (fun r =>
      (trace (R.density.op*(star r*r))).re)).sum=0 := by
  apply List.sum_eq_zero
  intro x hx
  rcases List.mem_map.mp hx with ⟨r,hr,he⟩
  rw [← he,application_residual_zero R r hr,star_zero Op,mul_zero,mul_zero]
  simp [trace,entry]

/-- There is no finite exact input to the completeness direction: four
orthogonal isometries exclude finite nonzero supports, as already proved in
TreeBasic. This closes the finite-realization implication without any compiler
or soundness assumption. -/
theorem finite_realization_completeness {P : Presentation} (R : NormalRealization P)
    (hR : FiniteRealization R) : HasFinitePerfect (CompilerScaffold.finalGame P) := by
  exact (TreeBasic.no_finite R hR).elim

#print axioms structural
#print axioms application_residual_zero
#print axioms residual_energy_zero
#print axioms finite_realization_completeness
end Sigma2.CompilerHonestRealization
