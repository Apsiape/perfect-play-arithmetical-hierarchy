import Sigma2.MainPaper

namespace Sigma2

/-- One total computable game family witnesses promised hardness for both languages. -/
def SharedFamilyHardness : Prop :=
  ∀ S, SigmaTwo S → ∃ f : ℕ → ℕ, Computable f ∧
    (∀ e, PromisedGame (f e)) ∧
    (∀ e, S e ↔ SpatialPerfect (f e)) ∧
    (∀ e, S e ↔ EntropyPerfect (f e))

theorem theoremA_shared_family : SharedFamilyHardness := by
  obtain ⟨f,hC⟩ := CompilerContract.lemma_4_4_strong_of_obligations
    CompilerObligations.obligations_all
  intro S hS
  obtain ⟨R,hR,h⟩ := hS
  exact ⟨CompiledReduction.gameCode f R hR,
    CompiledReduction.gameCode_computable hC R hR,
    CompiledValue.reduction_promised hC R hR,
    (fun e => (h e).trans (CompiledReduction.theorem_7_1_reduction hC R hR e).1.symm),
    (fun e => (h e).trans (CompiledReduction.theorem_7_1_reduction hC R hR e).2.1.symm)⟩

end Sigma2

namespace Sigma2

/-- Printed Definition 4.4, exposed to the independent comparator. -/
theorem paper_admissible_iff (P : Presentation) :
    PaperAdmissible P ↔ P.admissible ∧ P.root ∈ P.transported ∧
      ∀ row ∈ P.linear, ∀ r ∈ row, ∀ i ∈ r.1.labels, i ∈ P.transported := Iff.rfl

end Sigma2
