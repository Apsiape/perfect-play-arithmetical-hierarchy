import Sigma2.CompilerApproxDictionaryEnergy
import Sigma2.CompilerApproxDecoder

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxDictionaryBound
open Compiler CompilerScaffold CompilerEventCounting CompilerEventLoss CompilerEventClasses
  CompilerEvents CompilerEventSlots CompilerApproxDictionaryIndex CompilerApproxDictionaryEnergy CompilerApproxDecoder
attribute [local irreducible] names rowList words polynomials structuralPolynomials applicationPolynomials rowsBefore

local instance rowNeZero (P : Presentation) : NeZero (RowSlots.dimension (rows P)) :=
  ⟨ne_of_gt (RowSlots.dimension_pos (rows P))⟩

def rowContribution (P : Presentation) (S : NormalStrategy (finalGame P).scenario)
    (r : Fin (rows P).rowCount) : ℝ :=
  bothZeroContribution P S
    (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
    (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
    (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
    (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r))

def HonestApplicationRows (P : Presentation) (R : StructuralRealization P)
    (S : NormalStrategy (finalGame P).scenario) : Prop :=
  ∃ s₀ : Scenario,∃ S₀ : NormalStrategy s₀,∀ j : Fin (applicationPolynomials P).length,
    HonestRow (RowSlots.dimension (rows P)) S₀ S (oldDensity R)
      (slotFamily (rows P) (numbered R) (rowIndex P j))
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) (rowIndex P j)))
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) (rowIndex P j)))

def baseWeight (P : Presentation) (j : Fin (applicationPolynomials P).length) : ℝ :=
  16*(RowSlots.denominator (RowSlots.coefficients (rows P) (rowIndex P j)):ℝ)^2/363/
    (RowSlots.dimension (rows P):ℝ)^3/(questionCount P:ℝ)^2

def energyAt (P : Presentation) (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) : ℝ :=
  (trace (R.density.op*(star (residualAt P R j)*residualAt P R j))).re

def energyTotal (P : Presentation) (R : StructuralRealization P) : ℝ := ∑ j,energyAt P R j

theorem energy_nonnegative (h : Density) (A : Op) :
    0≤(trace (h.op*(star A*A))).re := by
  have hp : Positive (star A*A) := ContinuousLinearMap.isPositive_adjoint_comp_self A
  have ht := TraceProducts.covariance_mul_trace (TraceProducts.rootFamily h)
    (TraceProducts.root_summable h) (star A*A) hp
  rw [TraceProducts.density_eq_covariance,ht.2.1,Complex.re_tsum ht.2.2]
  exact tsum_nonneg (fun k => hp.re_inner_nonneg_left _)

theorem sum_indexed {α : Type} (xs : List α) (n : ℕ) (hn : xs.length=n) (f : α → ℝ) :
    (∑ j : Fin n,f (xs[j.val]'(by rw [hn]; exact j.isLt)))=(xs.map f).sum := by
  subst n
  rw [← List.sum_ofFn]
  exact congrArg List.sum (List.ofFn_getElem_eq_map _ _)

theorem energyTotal_residuals (P : Presentation) (R : StructuralRealization P) :
    energyTotal P R=((applicationResiduals P R).map (fun A => (trace (R.density.op*(star A*A))).re)).sum := by
  have hs := sum_indexed (CompilerApproxMatching.entries P R)
    (applicationPolynomials P).length (CompilerApproxMatching.entries_length P R)
    (fun t : CompilerApproxMatching.Entry => (trace (R.density.op*(star t.2.2.2*t.2.2.2))).re)
  calc
    energyTotal P R=((CompilerApproxMatching.entries P R).map
      (fun t => (trace (R.density.op*(star t.2.2.2*t.2.2.2))).re)).sum := hs
    _=_ := by rw [← CompilerApproxMatching.entries_residuals,List.map_map]; rfl

theorem energyAt_le (P : Presentation) (R : StructuralRealization P)
    (j : Fin (applicationPolynomials P).length) : energyAt P R j≤energyTotal P R :=
  Finset.single_le_sum (fun i hi => energy_nonnegative R.density _) (Finset.mem_univ j)

theorem baseWeight_nonnegative (P : Presentation) (j : Fin (applicationPolynomials P).length) :
    0≤baseWeight P j := by unfold baseWeight; positivity

theorem row_loss (P : Presentation) (hP : P.admissible) (R : StructuralRealization P)
    (S : NormalStrategy (finalGame P).scenario) (hS : HonestApplicationRows P R S)
    (j : Fin (applicationPolynomials P).length) :
    rowContribution P S (rowIndex P j)=baseWeight P j*beta P R j*energyAt P R j := by
  obtain ⟨s₀,S₀,H⟩ := hS
  let r := rowIndex P j
  let A := rowOperator (rows P) (numbered R) r
  let L := RowSlots.denominator (RowSlots.coefficients (rows P) r)
  have hA : star A=A := rowOperator_selfadjoint _ _ (numbered_projection R) r
  have hp := row_zero_probabilities _ S₀ S (oldDensity R)
    (slotFamily (rows P) (numbered R) r) _ _ _ _ (H j)
    (slotFamily_selfadjoint _ _ (numbered_projection R) r)
  dsimp only at hp
  unfold rowContribution
  rw [actual_both_zero_weight P r S _ hp.1 hp.2,slotFamily_sum]
  have hop : star ((2*(L:ℂ)) • A)*((2*(L:ℂ)) • A)=(4*(L:ℂ)^2) • (A*A) := by
    rw [star_smul,hA]
    simp only [star_mul,star_ofNat,star_natCast,smul_mul_smul_comm]
    congr 1
    ring
  change 2*((1/(RowSlots.dimension (rows P):ℝ)^3)*
    (trace ((oldDensity R).op*(star ((2*(L:ℂ)) • A)*((2*(L:ℂ)) • A)))).re)/(questionCount P:ℝ)^2=_
  rw [hop,mul_smul_comm,CompilerAlgebra.trace_smul]
  have hc : (4*(L:ℂ)^2)=((4*(L:ℝ)^2:ℝ):ℂ) := by push_cast; rfl
  rw [hc]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have he := residual_matching P hP R j
  change (trace ((oldDensity R).op*(A*A))).re=_ at he
  rw [he]
  dsimp only [baseWeight,energyAt,L,r]
  ring

theorem row_bound (P : Presentation) (hP : P.admissible) (R : StructuralRealization P)
    (S : NormalStrategy (finalGame P).scenario) (hS : HonestApplicationRows P R S)
    (j : Fin (applicationPolynomials P).length) :
    rowContribution P S (rowIndex P j)≤(16*∑ i,baseWeight P i)*energyTotal P R := by
  rw [row_loss P hP R S hS]
  have hw := baseWeight_nonnegative P j
  have hb := beta_le P R j
  have he := energy_nonnegative R.density (residualAt P R j)
  have he' := energyAt_le P R j
  have ht : 0≤energyTotal P R := Finset.sum_nonneg (fun i hi => energy_nonnegative R.density _)
  have hs : baseWeight P j≤∑ i,baseWeight P i :=
    Finset.single_le_sum (fun i hi => baseWeight_nonnegative P i) (Finset.mem_univ j)
  calc
    _≤baseWeight P j*16*energyAt P R j := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb hw) he
    _≤baseWeight P j*16*energyTotal P R := mul_le_mul_of_nonneg_left he' (mul_nonneg hw (by norm_num))
    _≤(16*∑ i,baseWeight P i)*energyTotal P R := mul_le_mul_of_nonneg_right (by nlinarith) ht

#print axioms energy_nonnegative
#print axioms energyTotal_residuals
#print axioms row_loss
#print axioms row_bound
end Sigma2.CompilerApproxDictionaryBound
