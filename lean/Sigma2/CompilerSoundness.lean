import Sigma2.CompilerSoundnessApplications
import Sigma2.CompilerSoundnessFinite
import Sigma2.CompilerContract

/-! The four exact frozen soundness propositions, for admissible presentations. -/
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundness
open Compiler CompilerScaffold CompilerSoundnessExtraction CompilerSoundnessIntertwiners
  CompilerSoundnessSourceOperators CompilerSoundnessTyping CompilerSoundnessApplications
  CompilerSoundnessFinalExtraction CompilerSoundnessFinite Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
  CompilerSoundnessSource.support
variable {P : Presentation}

def realization (E : SupportedScaffold P) (hP : P.admissible) : NormalRealization P where
  support := CompilerSoundnessSource.support E
  support_projection := CompilerSoundnessSource.support_projection E
  density := CompilerSoundnessSource.density E
  density_supported := (CompilerSoundnessSource.density_support E).2.1
  faithful_on := (CompilerSoundnessSource.density_support E).2.2
  label := returnedLabel E
  creation := returnedCreation E
  label_supported := by simpa only [source_eq] using returnedLabel_supported E
  creation_supported := by simpa only [source_eq] using returnedCreation_supported E
  typed := returnedLabel_typed E
  centralizer := returnedLabel_central E
  isometries := by simpa only [source_eq] using returned_isometries E
  ranges := by
    have hr : P.root<P.types.length := (List.getElem?_eq_some_iff.mp hP.1).1
    simpa only [source_eq] using returned_ranges E hr
  modular := returnedCreation_modular E
  central_equations := by
    intro p hp
    simpa only [source_eq] using central_equation E p hp (hP.2.2.1 p hp)
  endpoint_equations := by
    intro r hr
    simpa only [source_eq] using endpoint_equation E r hr
      (fun i hi => hP.2.1 i ((hP.2.2.2.1 r hr).1 i hi)) ((hP.2.2.2.1 r hr).2)
  zero_equations := by
    intro r hr
    simpa only [source_eq] using zero_equation E r hr
      (fun i hi => hP.2.1 i (hP.2.2.2.2.1 r hr i hi))
  linear_equations := by
    intro row hr
    simpa only [source_eq] using linear_equation E row hr (hP.2.2.2.2.2 row hr)

theorem soundness (P : Presentation) (hP : P.admissible) : CompilerContract.Soundness P := by
  rintro ⟨T,hT⟩
  obtain ⟨E,_,_⟩ := CompilerSoundnessExtraction.of_final P T hT
  exact ⟨realization E hP⟩

theorem finiteEntropySoundness (P : Presentation) (hP : P.admissible) :
    CompilerContract.FiniteEntropySoundness P := by
  rintro ⟨T,hT,hEnt⟩
  obtain ⟨E,_,hEntE⟩ := CompilerSoundnessExtraction.of_final P T hT
  exact ⟨realization E hP,CompilerSoundnessSource.density_finite_of_strategy E (hEntE.mpr hEnt)⟩

theorem finiteSupportSoundness (P : Presentation) (hP : P.admissible) :
    CompilerContract.FiniteSupportSoundness P := by
  rintro ⟨S,d,hd,hfin,hS⟩
  obtain ⟨E,hv,hw,_⟩ := CompilerSoundnessFinalExtraction.of_final P (normalOfPure S) hS
  exact ⟨realization E hP,finite_source P S d hfin E hv hw⟩

theorem sourceEventSoundness (P : Presentation) (hP : P.admissible) :
    CompilerContract.SourceEventSoundness P := by
  refine ⟨sourceQuestion P,sourceAnswer P,?_⟩
  intro T hT
  obtain ⟨E,hv,hw,hsource⟩ := CompilerSoundnessFinalExtraction.of_final P T hT
  have hmass : (trace (E.densityA.op*CompilerSoundnessSource.support E)).re=1/121 := by
    unfold CompilerSoundnessSource.support
    exact CompilerSoundnessCover.supported_source_mass E
  refine ⟨realization E hP,E.densityA,E.supportA,?_,E.supportA_laws,hsource,
    CompilerSoundnessSource.density_formula E,hmass⟩
  exact (marginal_preserved E.strategy T hv hw E.densityA).mp E.marginalA

#print axioms realization
#print axioms soundness
#print axioms finiteEntropySoundness
#print axioms finiteSupportSoundness
#print axioms sourceEventSoundness
end Sigma2.CompilerSoundness
