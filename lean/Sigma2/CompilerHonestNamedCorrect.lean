import Sigma2.CompilerHonestPregameBase

/-! Concrete NamedBinaryProjections for the simultaneous pregame family.
The refinements remain independent: no pair of labels is assumed to commute. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerHonestNamedCorrect
open Compiler CompilerScaffold CompilerHonestState CompilerHonestFMSLift
  CompilerProjectionDictionary CompilerHonestCentralizer CompilerHonestPregameBase
  CoefficientOperator TensorLifts RowCompleteness Preliminaries PureSupport

attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

 theorem transposed_support (h : Density) (e : Op) (he : SupportOf h e) :
    SupportOf (transposedDensity h) (transpose e) := by
  have hr : h.op*e=h.op := by
    have hh := congrArg star he.2.1
    simpa only [star_mul,he.1.1,h.positive.isSelfAdjoint.star_eq] using hh
  refine ⟨transpose_projection e he.1,?_,?_⟩
  · change transpose e*transpose h.op=transpose h.op
    rw [← transpose_mul,hr]
  · intro v hv hz
    change star (star e (star v))=v at hv
    change star (star h.op (star v))=0 at hz
    rw [he.1.1] at hv
    rw [h.positive.isSelfAdjoint.star_eq] at hz
    have hv' := congrArg star hv
    have hz' := congrArg star hz
    simp only [star_star] at hv'
    simp only [star_star,star_zero] at hz'
    have hh := he.2.2 (star v) hv' hz'
    have hh' := congrArg star hh
    simpa only [star_star,star_zero] using hh'

 theorem compressed_projection (e E : Op) (he : Projection e) (hE : Projection E)
    (hc : E*e=e*E) : BinaryProjectionOn e E := by
  refine ⟨hc,?_⟩
  have heq : e*E*e=e*E := by rw [mul_assoc,hc,← mul_assoc,he.2]
  rw [heq]
  exact projection_product e E he hE hc.symm

 theorem binary_mirrors (h : Density) (E : Op) (hE : Projection E)
    (hc : Centralizes h.op E) (a : Answers) :
    left ((CompilerHonestPregameBase.binary E hE).effect a) (CompilerHonestState.vector h)=
      right ((CompilerHonestPregameBase.binary (transpose E) (transpose_projection E hE)).effect a)
        (CompilerHonestState.vector h) := by
  apply coarse_mirror
  intro b
  exact binary_mirror E (transpose E) hE (transpose_projection E hE)
    (CompilerHonestState.vector h) (mirror h E hc) b

 theorem partition_rejection {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Partition Op ι) (v : AB)
    (hm : ∀ b,left (A.effect b) v=right (B.effect b) v)
    (a b : ι) (hab : a≠b) : (left (A.effect a)*right (B.effect b)) v=0 := by
  change left (A.effect a) (right (B.effect b) v)=0
  rw [← hm b]
  change (left (A.effect a)*left (A.effect b)) v=0
  rw [← left_mul,A.orthogonal a b hab,CoarseCells.left_zero,zero_apply]

 theorem synchronized {P : Presentation} (R : StructuralRealization P) (A B : Refinements)
    (i : Fin (names P).length) : BinaryEventSynchronized (CompilerHonestPregameBase.strategy R A B) (event P i) := by
  intro a b hm
  have hab : a≠b := by
    intro hh
    subst b
    exact hm Iff.rfl
  let E := CompilerOrientedProjections.projection R ((names P)[i.val]'i.isLt)
  have hE : Projection E := CompilerOrientedProjections.projection_projective R _
  have hz := partition_rejection (CompilerHonestPregameBase.binary E hE)
    (CompilerHonestPregameBase.binary (transpose E) (transpose_projection E hE))
    (CompilerHonestState.vector (density R.density))
    (binary_mirrors (density R.density) E hE (CompilerOrientedProjections.projection_centralizer R _)) a b hab
  rw [CompilerHonestPregameBase.strategy,CompilerHonestState.strategy,normalOfPure_probability]
  change (inner ℂ (CompilerHonestState.vector (density R.density))
    (((CompilerHonestPregameBase.measurements R A B).left (event P i).x a*
      (CompilerHonestPregameBase.measurements R A B).right (event P i).y b)
        (CompilerHonestState.vector (density R.density)))).re=0
  rw [measurements_left,measurements_right]
  change (inner ℂ (CompilerHonestState.vector (density R.density))
    ((left ((localPartition R false A (question P i.val)).effect a)*
      right ((localPartition R true B (question P i.val)).effect b))
        (CompilerHonestState.vector (density R.density)))).re=0
  rw [question_name]
  change (inner ℂ (CompilerHonestState.vector (density R.density))
    ((left ((CompilerHonestPregameBase.binary E hE).effect a)*
      right ((CompilerHonestPregameBase.binary (transpose E) (transpose_projection E hE)).effect b))
        (CompilerHonestState.vector (density R.density)))).re=0
  rw [hz,inner_zero_right]
  rfl

/-- Every actual named binary event has a reducing projective compression on
both genuine marginal supports, and zero disagreement probability. -/
theorem namedBinaryProjections {P : Presentation} (R : StructuralRealization P) (A B : Refinements) :
    NamedBinaryProjections (rows P) (CompilerHonestPregameBase.strategy R A B) := by
  let h := density R.density
  obtain ⟨e,he⟩ := support_exists h
  have hmA := CompilerHonestState.marginalA h (CompilerHonestPregameBase.measurements R A B)
  have hmB := CompilerHonestState.marginalB h (CompilerHonestPregameBase.measurements R A B)
  refine ⟨h,transposedDensity h,e,transpose e,hmA,hmB,he,transposed_support h e he,?_,?_⟩
  · intro i
    change BinaryProjectionOn e ((CompilerHonestPregameBase.strategy R A B).measurements.alice
      (event P i).x (event P i).a) ∧
      BinaryProjectionOn (transpose e) ((CompilerHonestPregameBase.strategy R A B).measurements.bob
        (event P i).y (event P i).b)
    let E := CompilerOrientedProjections.projection R ((names P)[i.val]'i.isLt)
    have hE : Projection E := CompilerOrientedProjections.projection_projective R _
    have hc : E*e=e*E := matching_commutes_support
      (⟨CompilerHonestPregameBase.measurements R A B,CompilerHonestState.vector h,vector_unit h⟩ : PureStrategy (scenario P))
      h hmA e he E (transpose E) (ContinuousLinearMap.IsPositive.of_isStarProjection ⟨hE.2,hE.1⟩)
      (mirror h E (CompilerOrientedProjections.projection_centralizer R _))
    have hct := congrArg transpose hc
    rw [transpose_mul,transpose_mul] at hct
    have hleft := compressed_projection e E he.1 hE hc
    have hright := compressed_projection (transpose e) (transpose E) (transpose_projection e he.1)
      (transpose_projection E hE) hct.symm
    exact ⟨Eq.mpr (congrArg (BinaryProjectionOn e) (CompilerHonestPregameBase.namedA R A B i)) hleft,
      Eq.mpr (congrArg (BinaryProjectionOn (transpose e)) (CompilerHonestPregameBase.namedB R A B i)) hright⟩

  · exact synchronized R A B

#print axioms transposed_support
#print axioms synchronized
#print axioms namedBinaryProjections
end Sigma2.CompilerHonestNamedCorrect
