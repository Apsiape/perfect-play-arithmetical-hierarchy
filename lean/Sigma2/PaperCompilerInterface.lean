import Sigma2.PaperAdmissibility
import Sigma2.CompilerHardness

noncomputable section
namespace Sigma2
open PaperAdmissibility

/-- The concrete, computable all-label compiler needs its mathematical contract
only on presentations satisfying printed Definition 4.4 literally.  Its game
and code are provably unchanged by transport saturation. -/
theorem theoremA_of_paper_compiler
    (hC : ∀ P, PaperAdmissible P →
      Compiler.Compiled P (CompilerScaffold.codeFor P) ∧
        Compiler.ApproxCompiled P (CompilerScaffold.codeFor P)) : TheoremAStatement := by
  apply theoremA_of_compiler (f := CompilerScaffold.codeMap)
  refine ⟨CompilerEffectiveCoding.codeMap_computable, ?_⟩
  intro code P hd hP
  have hc : CompilerScaffold.codeMap code = CompilerScaffold.codeFor P := by
    simp only [CompilerScaffold.codeMap, hd]
  rw [hc]
  obtain ⟨he, ha⟩ := hC (saturate P) (saturation_paper_admissible P hP)
  rw [saturation_codeFor P] at he ha
  exact ⟨compiled_of_saturated P _ he, approxCompiled_of_saturated P _ ha⟩

/-- The corresponding seven-obligation interface has the literal paper domain.
This conditional wrapper does not discharge any of the seven obligations. -/
theorem theoremA_of_paper_obligations
    (hO : ∀ P, PaperAdmissible P → CompilerContract.Obligations P) : TheoremAStatement := by
  apply theoremA_of_paper_compiler
  intro P hP
  have h := hO P hP
  exact ⟨CompilerContract.compiled_of_obligations P h, h.2.2.2.2.2.2⟩

end Sigma2

#print Sigma2.theoremA_of_paper_compiler
#print Sigma2.theoremA_of_paper_obligations
#print axioms Sigma2.theoremA_of_paper_compiler
#print axioms Sigma2.theoremA_of_paper_obligations
