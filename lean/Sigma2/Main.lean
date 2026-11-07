import Sigma2.CompilerHardness
import Sigma2.CompilerObligations

namespace Sigma2

/-- Theorem A, with no hypotheses. -/
theorem theoremA : TheoremAStatement :=
  theoremA_of_obligations CompilerObligations.obligations_all

end Sigma2
