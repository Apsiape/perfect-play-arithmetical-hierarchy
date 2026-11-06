import Sigma2.CompilerSoundness
import Sigma2.CompilerHonestStructuralAssembly
import Sigma2.CompilerCompleteness

namespace Sigma2.CompilerObligations

/-- All seven frozen compiler obligations, with no compiler-contract hypothesis. -/
theorem obligations_all : ∀ P, P.admissible → CompilerContract.Obligations P := by
  intro P hP
  exact CompilerCompleteness.obligations_of_base15 P hP
    (CompilerHonestBase.baseObligation15 P)
    (CompilerSoundness.soundness P hP)
    (CompilerSoundness.finiteEntropySoundness P hP)
    (CompilerSoundness.finiteSupportSoundness P hP)
    (CompilerSoundness.sourceEventSoundness P hP)

end Sigma2.CompilerObligations

#print axioms Sigma2.CompilerObligations.obligations_all
