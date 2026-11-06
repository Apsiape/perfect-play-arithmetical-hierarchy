import Sigma2.PaperCompilerInterface
import Sigma2.CompilerObligations

namespace Sigma2

/-- The literal Definition-4.4 route with its compiler obligations discharged. -/
theorem theoremA_of_tarski_paper (hT : UpperRealArithmetic.TarskiDecision) :
    TheoremAStatement :=
  theoremA_of_tarski_of_paper_obligations
    (fun P hP => CompilerObligations.obligations_all P hP.1) hT

end Sigma2

#print axioms Sigma2.theoremA_of_tarski_paper
