import Sigma2.CompilerSoundnessLabels
import Sigma2.CompilerSoundnessChain
import Sigma2.CompilerSoundnessSource

/-! Concrete returned operators on the full named source. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessSourceOperators
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessLift CompilerSoundnessDictionary
  CompilerSoundnessIntertwiners CompilerSoundnessBridgeCopies CompilerSoundnessBridgeFrame
  CompilerSoundnessLabels CompilerSoundnessChain CompilerSoundnessPolynomials
  CompilerSoundnessBlockEquations Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

theorem evalPoly_central (E : SupportedScaffold P) (p : Poly) :
    Commute E.densityA.op (evalPoly (CompilerSoundnessWordEvaluation.unitaries E) p) := by
  induction p with
  | nil => exact Commute.zero_right _
  | cons t p ih => exact ((show Commute E.densityA.op (evalWord (CompilerSoundnessWordEvaluation.unitaries E) t.2) from evalWord_central E t.2).smul_right (t.1:ℂ)).add_right ih

theorem fullValue_central (E : SupportedScaffold P) (p : Poly) :
    Commute E.densityA.op (fullValue E p) := by
  apply spread_commutes E _ _ E.densityA.positive.isSelfAdjoint
  · intro i
    fin_cases i
    · exact E.frame.2.2 0
    · have hc : Commute E.densityA.op (CompilerSoundnessGraphs.graphBlock (projectionA P E.strategy E.supportA) [] 0) := graphBlock_central E [] 0
      simpa [CompilerSoundnessLift.gauge] using hc
    · change Commute E.densityA.op (CompilerSoundnessGraphs.graphBlock (projectionA P E.strategy E.supportA) [] 1)
      exact graphBlock_central E [] 1
  · exact (evalPoly_central E p).mul_right (E.frame.2.2 0)

def returnedLabel (E : SupportedScaffold P) (i : ℕ) : Op :=
  if i<P.types.length then CompilerSoundnessLabels.label E 0 i else 0

def submittedCreation (E : SupportedScaffold P) (a : Fin 4) : Op :=
  fullValue E (creation P a.val)

def returnedCreation (E : SupportedScaffold P) (a : Fin 4) : Op :=
  star (chain E)*submittedCreation E a

theorem returnedLabel_supported (E : SupportedScaffold P) (i : ℕ) :
    corner E 0*returnedLabel E i=returnedLabel E i ∧ returnedLabel E i*corner E 0=returnedLabel E i := by
  unfold returnedLabel
  split_ifs with hi
  · exact label_supported E 0 ⟨i,hi⟩
  · simp

theorem returnedLabel_original_central (E : SupportedScaffold P) (i : ℕ) :
    Commute E.densityA.op (returnedLabel E i) := by
  unfold returnedLabel
  split_ifs
  · exact fullValue_central E _
  · exact Commute.zero_right _

theorem source_eq (E : SupportedScaffold P) : CompilerSoundnessSource.support E=corner E 0 := rfl

theorem returnedLabel_central (E : SupportedScaffold P) (i : ℕ) :
    Centralizes (CompilerSoundnessSource.density E).op (returnedLabel E i) := by
  have hc := (returnedLabel_original_central E i).eq
  have hs := returnedLabel_supported E i
  change ((121:ℂ) • (E.densityA.op*CompilerSoundnessSource.support E))*returnedLabel E i=
    returnedLabel E i*((121:ℂ) • (E.densityA.op*CompilerSoundnessSource.support E))
  rw [source_eq,smul_mul_assoc,mul_smul_comm,mul_assoc,hs.1]
  congr 1
  calc
    _=returnedLabel E i*E.densityA.op := hc
    _=returnedLabel E i*(corner E 0*E.densityA.op) := by rw [← mul_assoc,hs.2]
    _=returnedLabel E i*(E.densityA.op*corner E 0) := by
      have hh := (CompilerSoundnessSource.source_central E).eq
      rw [source_eq] at hh
      rw [hh]

theorem creation_structural_mem (P : Presentation) (a : Fin 4) :
    sub (creation P a.val) (mul (mul (e 4) (creation P a.val)) (e 0)) ∈ structuralPolynomials P := by
  simp only [structuralPolynomials,List.mem_append]
  right
  exact List.mem_map.mpr ⟨a.val,List.mem_range.mpr a.isLt,rfl⟩

theorem rectangular_support (C e f : Op) (he : Projection e) (hf : Projection f) (h : C=e*C*f) :
    e*C=C ∧ C*f=C := by
  constructor
  · calc
      _=e*(e*C*f) := congrArg (fun X : Op => e*X) h
      _=C := by rw [← mul_assoc,← mul_assoc,he.2,← h]
  · calc
      _=(e*C*f)*f := congrArg (fun X : Op => X*f) h
      _=C := by rw [mul_assoc,mul_assoc,hf.2,← mul_assoc,← h]

theorem submittedCreation_supported (E : SupportedScaffold P) (a : Fin 4) :
    corner E 4*submittedCreation E a=submittedCreation E a ∧
      submittedCreation E a*corner E 0=submittedCreation E a := by
  have hp := full_polynomial_equations E _ (show sub (creation P a.val)
      (mul (mul (e 4) (creation P a.val)) (e 0)) ∈ polynomials P from by
    simp only [polynomials,List.mem_append]; exact Or.inl (creation_structural_mem P a))
  have h4 : fullValue E (e 4)=corner E 4 := fullValue_e E 4
  have h0 : fullValue E (e 0)=corner E 0 := fullValue_e E 0
  rw [fullValue_sub,fullValue_mul,fullValue_mul,h4,h0] at hp
  apply rectangular_support _ _ _ (corner_projection E _) (corner_projection E _)
  exact sub_eq_zero.mp hp

theorem returnedCreation_supported (E : SupportedScaffold P) (a : Fin 4) :
    corner E 0*returnedCreation E a=returnedCreation E a ∧
      returnedCreation E a*corner E 0=returnedCreation E a := by
  have hs : corner E 0*star (chain E)=star (chain E) := by
    simpa only [star_mul,(corner_projection E _).1] using
      congrArg (fun A : Op => star A) (chain_partial E).right
  constructor
  · change corner E 0*(star (chain E)*submittedCreation E a)=_
    rw [← mul_assoc,hs]
    rfl
  · change (star (chain E)*submittedCreation E a)*corner E 0=_
    rw [mul_assoc,(submittedCreation_supported E a).2]
    rfl

/-- Exact modular factor for the concrete returned creation operator, using
the full normalized source density already constructed in stage 25. -/
theorem returnedCreation_modular (E : SupportedScaffold P) (a : Fin 4) :
    (CompilerSoundnessSource.density E).op*returnedCreation E a=
      (1/16:ℂ) • (returnedCreation E a*(CompilerSoundnessSource.density E).op) := by
  have hC : E.densityA.op*submittedCreation E a=submittedCreation E a*E.densityA.op := (fullValue_central E _).eq
  have hT : E.densityA.op*returnedCreation E a=(1/16:ℂ) • (returnedCreation E a*E.densityA.op) := by
    change E.densityA.op*(star (chain E)*submittedCreation E a)=_
    rw [← mul_assoc,chain_adjoint_modular,smul_mul_assoc,mul_assoc,hC]
    simp only [returnedCreation,mul_assoc]
  have hs := returnedCreation_supported E a
  have hc : E.densityA.op*corner E 0=corner E 0*E.densityA.op := by
    simpa only [source_eq] using (CompilerSoundnessSource.source_central E).eq
  have hl : (CompilerSoundnessSource.density E).op*returnedCreation E a=
      (121:ℂ) • (E.densityA.op*returnedCreation E a) := by
    change ((121:ℂ) • (E.densityA.op*CompilerSoundnessSource.support E))*returnedCreation E a=_
    rw [source_eq,smul_mul_assoc,mul_assoc,hs.1]
  have hr : returnedCreation E a*(CompilerSoundnessSource.density E).op=
      (121:ℂ) • (returnedCreation E a*E.densityA.op) := by
    change returnedCreation E a*((121:ℂ) • (E.densityA.op*CompilerSoundnessSource.support E))=_
    rw [source_eq,mul_smul_comm,hc,← mul_assoc,hs.2]
  rw [hl,hr,hT]
  module

#print axioms fullValue_central
#print axioms returnedLabel_supported
#print axioms returnedLabel_central
#print axioms submittedCreation_supported
#print axioms returnedCreation_supported
#print axioms returnedCreation_modular
end Sigma2.CompilerSoundnessSourceOperators
