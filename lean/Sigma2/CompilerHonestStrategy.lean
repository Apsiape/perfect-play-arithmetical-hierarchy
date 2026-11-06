import Sigma2.CompilerHonestEvent
import Sigma2.CompilerHonestPregameClass
import Sigma2.CompilerHonestPolynomialCorrect

/-! stage 15 corrected honest strategy entry point. The base strategy is
 CompilerHonestRefinementsCorrect.strategy; its full pregame perfection is
 CompilerHonestPregameCorrect.perfect. The explicit final strategy is
 CompilerHonestFinalCorrect.finalStrategy; honestRow supplies all eight fields
 of the compiler development's exact record for every row and arbitrary structural R.
 RowsHold, the remaining structural row equations, final-game perfection,
 Completeness, FiniteEntropyCompleteness, and ApproxCompiled are not asserted. -/
