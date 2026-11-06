import Sigma2.CompilerHardness
import Sigma2.CompilerObligations

namespace Sigma2

/-- Theorem A with the published real-arithmetic decision input explicit. -/
theorem theoremA_of_tarski (hT : UpperRealArithmetic.TarskiDecision) : TheoremAStatement :=
  theoremA_of_tarski_of_obligations CompilerObligations.obligations_all hT

end Sigma2
