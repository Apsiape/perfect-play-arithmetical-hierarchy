import Sigma2.CompilerHonestFinalCorrect

/-! The compiler development's coefficient-eight theorem applied to the actual
 corrected honest strategy, for every structural realization and every row. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerHonestEvent
open Compiler CompilerScaffold CompilerEventCounting CompilerEventSlots
  CompilerHonestFinalCorrect CompilerHonestFMSLift

 theorem row_loss_identity {P : Presentation} (R : StructuralRealization P)
    (r : Fin (rows P).rowCount) :
    bothZeroContribution P (finalStrategy R)
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r))=
      8*(RowSlots.denominator (RowSlots.coefficients (rows P) r):ℝ)^2/
        (RowSlots.dimension (rows P):ℝ)^3/(questionCount P:ℝ)^2*
          (trace ((density R.density).op*
            (rowOperator (rows P) (aliceNames R) r*rowOperator (rows P) (aliceNames R) r))).re :=
  actual_slot_row_loss P r (CompilerHonestRefinementsCorrect.strategy R) (finalStrategy R)
    (density R.density) (aliceNames R) (aliceNames_projective R)
    (fun _ => CompilerOrientedProjections.projection_centralizer R _) (honestRow R r)

#print axioms row_loss_identity
end Sigma2.CompilerHonestEvent
