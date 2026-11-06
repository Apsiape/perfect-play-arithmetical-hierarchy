import Sigma2.CoefficientOperator
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CoefficientOperator
open Coefficients TensorLifts PureSupport Preliminaries

/-- Faithfulness is only required on the indicated corner. No trace-one
normalization and no injectivity on the coefficient domain are required. -/
theorem covariance_kernel_eq (D P : Op) (hP : Projection P)
    (hPD : P*D=D) (hDP : D*P=D)
    (hf : ∀ x,P x=x → D x=0 → x=0) : D.ker=P.ker := by
  ext x
  change D x=0 ↔ P x=0
  constructor
  · intro hx
    apply hf (P x)
    · exact congrArg (fun T : Op => T x) hP.2
    · change (D*P) x=0
      rw [hDP,hx]
  · intro hx
    have hh := congrArg (fun T : Op => T x) hDP
    change D (P x)=D x at hh
    simpa only [hx,map_zero] using hh.symm

/-- The coefficient map has dense range in precisely the stated support.
This is the corner form of N3, valid for noninjective coefficient maps. -/
theorem range_closure (T D P : Op) (hT : T*star T=D) (hP : Projection P)
    (hPD : P*D=D) (hDP : D*P=D)
    (hf : ∀ x,P x=x → D x=0 → x=0) :
    T.range.topologicalClosure=P.range := by
  have hk : (star T).ker=P.ker := by
    calc
      _ = (T*star T).ker := T.ker_self_comp_adjoint.symm
      _ = D.ker := by rw [hT]
      _ = P.ker := covariance_kernel_eq D P hP hPD hDP hf
  have ht : (star T).kerᗮ=T.range.topologicalClosure := by
    have hh := (star T).orthogonal_ker
    change (star T).kerᗮ=(star (star T)).range.topologicalClosure at hh
    simpa only [star_star] using hh
  have hp : P.kerᗮ=P.range.topologicalClosure := by
    have hh := P.orthogonal_ker
    change P.kerᗮ=(star P).range.topologicalClosure at hh
    rwa [hP.1] at hh
  rw [← ht,hk,hp]
  exact (ContinuousLinearMap.IsIdempotentElem.isClosed_range hP.2).submodule_topologicalClosure_eq

theorem original_range_closure {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    (coefficient S.vector).range.topologicalClosure=P.range := by
  have hr : h.op*P=h.op := by
    have hh := congrArg star hP.2.1
    simpa only [star_mul,hP.1.1,h.positive.isSelfAdjoint.star_eq] using hh
  exact range_closure _ h.op P (coefficient_marginal S h hm) hP.1 hP.2.1 hr hP.2.2

/-- Cancel a bounded operator on a dense corner range. -/
theorem cancel_on_range (A T P : Op) (hT : T.range.topologicalClosure=P.range)
    (hz : A*T=0) : A*P=0 := by
  have hr : T.range ≤ A.ker := by
    rintro _ ⟨x,rfl⟩
    exact congrArg (fun B : Op => B x) hz
  have hc : T.range.topologicalClosure ≤ A.ker :=
    Submodule.topologicalClosure_minimal _ hr A.isClosed_ker
  rw [hT] at hc
  apply ContinuousLinearMap.ext
  intro x
  exact hc ⟨x,rfl⟩

/-- A reducing marginal corner has its actual, possibly noninjective,
coefficient map with dense range in that corner. -/
theorem corner_coefficient {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (E : Op) (hE : Projection E) (hEP : E*P=E) (hc : h.op*E=E*h.op) :
    let T := coefficient (left E S.vector)
    T*star T=E*h.op ∧ T.range.topologicalClosure=E.range := by
  have heq : coefficient (left E S.vector)*star (coefficient (left E S.vector))=E*h.op := by
    rw [coefficient_left,star_mul,← mul_assoc,mul_assoc E,coefficient_marginal S h hm,hE.1]
    rw [mul_assoc E h.op E,hc,← mul_assoc,hE.2]
  refine ⟨heq,?_⟩
  apply range_closure _ (E*h.op) E heq hE
  · rw [← mul_assoc,hE.2]
  · rw [mul_assoc, hc,← mul_assoc,hE.2]
  · intro x hx hz
    apply hP.2.2 x
    · have hpE : P*E=E := by
        have hh := congrArg star hEP
        simpa only [star_mul,hP.1.1,hE.1] using hh
      have hh := congrArg (fun T : Op => T x) hpE
      change P (E x)=E x at hh
      simpa only [hx] using hh
    · have hh := congrArg (fun T : Op => T x) hc
      change h.op (E x)=E (h.op x) at hh
      rw [hx] at hh
      exact hh.trans hz

#print axioms original_range_closure
#print axioms cancel_on_range
end Sigma2.CoefficientOperator
