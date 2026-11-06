import Sigma2.RowCornerNormalization
import Sigma2.RowColumnContainment

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates

/-- The actual synchronized column total, including its padded zero answers,
    is transported to the supported diagonal corner identity. -/
theorem actual_column_blocks_total (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    (∑ a,matrixBlocks hu 0 (newEffects bob G R S.measurements P (columnQ R r) a))=
      Matrix.diagonal (fun _ => numericalUnit bob G R S.measurements P 0 0) := by
  dsimp only
  rw [← MatrixBlocks.sum,new_sum bob G R S.measurements P hP.1 _,MatrixBlocks.support]

/-- Actual column/graph forbidden products remain zero in precisely the
    numerical common-unit coordinates, for both original supports. -/
theorem actual_column_blocks_graph_zero (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a : Answer G R) (j : ℕ)
    (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool)
    (hne : eps≠parity (2*RowSlots.squares R) a.val j) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    matrixBlocks hu 0 (newEffects bob G R S.measurements P (columnQ R r) a)*
      matrixBlocks hu 0 (slotGraph bob G R S.measurements P r j hj eps)=0 := by
  dsimp only
  rw [← MatrixBlocks.mul _ _ _ _ (new_fine_supported bob G R S.measurements P hP.1 _ _).2,
    column_graph_zero bob G R S hS h hm P hP r a j hj eps hne,MatrixBlocks.zero]

/-- Original actual reference rejection, transported before any entrywise
    claim about the global-X reference is made. -/
theorem actual_column_blocks_reference_zero (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    matrixBlocks hu 0 (newEffects bob G R S.measurements P (columnQ R r) (zeroAnswer G R))*
      matrixBlocks hu 0 (newEffects bob G R S.measurements P (globalQ R true) (zeroAnswer G R))=0 := by
  dsimp only
  rw [← MatrixBlocks.mul _ _ _ _ (new_fine_supported bob G R S.measurements P hP.1 _ _).2,
    column_reference_zero bob G R S hS h hm P hP r,MatrixBlocks.zero]

theorem actual_column_blocks_orthogonal (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a b : Answer G R) (hab : a≠b) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    matrixBlocks hu 0 (newEffects bob G R S.measurements P (columnQ R r) a)*
      matrixBlocks hu 0 (newEffects bob G R S.measurements P (columnQ R r) b)=0 := by
  dsimp only
  rw [← MatrixBlocks.mul _ _ _ _ (new_fine_supported bob G R S.measurements P hP.1 _ _).2,
    new_fine_orthogonal bob G R S hS h hm P hP _ a b hab,MatrixBlocks.zero]

#print axioms actual_column_blocks_total
#print axioms actual_column_blocks_graph_zero
#print axioms actual_column_blocks_reference_zero
#print axioms actual_column_blocks_orthogonal
end Sigma2.RowScalar
