import Sigma2.CompilerHonestRefinementsCorrect
import Sigma2.CompilerHonestMarginalEntropy
noncomputable section
namespace Sigma2.CompilerHonestEntropyCorrect
open Compiler CompilerHonestState CompilerHonestFMSLift CompilerHonestRefinementsCorrect

theorem strategy_finite_entropy {P : Presentation} (R : StructuralRealization P)
    (hh : FiniteDensityEntropy R.density) : FiniteMarginalEntropy (strategy R) := by
  have he := CompilerHonestMarginalEntropy.density_finite_entropy R.density hh
  exact ⟨density R.density,transposedDensity (density R.density),
    CompilerHonestState.marginalA _ _,CompilerHonestState.marginalB _ _,
    he,CompilerHonestMarginalEntropy.transposed_finite_entropy _ he⟩
#print axioms strategy_finite_entropy
end Sigma2.CompilerHonestEntropyCorrect
