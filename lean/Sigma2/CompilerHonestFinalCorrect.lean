import Sigma2.CompilerHonestEntropyCorrect
import Sigma2.CompilerHonestPregameCorrect
import Sigma2.CompilerEventSlots
import Sigma2.RowCompletenessComplete

/-! An explicit final-game strategy for every StructuralRealization. Its
 literal columns and references discharge the compiler development's HonestRow record. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestFinalCorrect
open Compiler CompilerScaffold CompilerHonestRefinementsCorrect CompilerProjectionDictionary
  CompilerHonestCentralizer CompilerHonestState CompilerHonestFMSLift
  CompilerEventCounting CompilerEvents CompilerEventSlots CompilerEventState
  CoefficientOperator RowCompleteness TensorLifts FiniteAncilla
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

local instance (P : Presentation) : NeZero (RowSlots.dimension (rows P)) :=
  ⟨ne_of_gt (RowSlots.dimension_pos (rows P))⟩

def aliceNames {P : Presentation} (R : StructuralRealization P) (i : Fin (rows P).count) : Op :=
  CompilerOrientedProjections.projection R ((names P)[i.val]'i.isLt)
def bobNames {P : Presentation} (R : StructuralRealization P) (i : Fin (rows P).count) : Op :=
  transpose (aliceNames R i)

theorem aliceNames_projective {P : Presentation} (R : StructuralRealization P)
    (i : Fin (rows P).count) : Projection (aliceNames R i) := CompilerOrientedProjections.projection_projective R _
theorem bobNames_projective {P : Presentation} (R : StructuralRealization P)
    (i : Fin (rows P).count) : Projection (bobNames R i) :=
  transpose_projection _ (aliceNames_projective R i)

def measurements {P : Presentation} (R : StructuralRealization P) : Measurements (finalGame P).scenario :=
  honestMeasurements (preGame P) (rows P) (strategy R).measurements
    (aliceNames R) (bobNames R) (aliceNames_projective R) (bobNames_projective R)

def finalStrategy {P : Presentation} (R : StructuralRealization P) : NormalStrategy (finalGame P).scenario :=
  withMeasurements (RowSlots.dimension (rows P)) (strategy R) (measurements R)

theorem names_mirror {P : Presentation} (R : StructuralRealization P)
    (i : Fin (rows P).count) (k : ℕ) :
    left (aliceNames R i) ((strategy R).vector k)=right (bobNames R i) ((strategy R).vector k) :=
  mirror _ _ (CompilerOrientedProjections.projection_centralizer R _)

theorem alice_column {P : Presentation} (R : StructuralRealization P) (r : Fin (rows P).rowCount) :
    (finalStrategy R).measurements.alice (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r)) 0=
      matrixOp (RowSlots.dimension (rows P)) (zeroColumn (slotFamily (rows P) (aliceNames R) r)) := by
  change (measurements R).alice _ _=_
  rw [measurements,honest_A_effect,RowScalar.decode_qa]
  change (newPartition (preGame P) (rows P) (aliceNames R) (aliceNames_projective R) (.column r)).effect 0=_
  exact (column_effect (preGame P) (rows P) (aliceNames R) (aliceNames_projective R) r 0 0 rfl).trans
    (congrArg (matrixOp _) (rowColumn_zero (rows P) (aliceNames R) r))

theorem bob_column {P : Presentation} (R : StructuralRealization P) (r : Fin (rows P).rowCount) :
    (finalStrategy R).measurements.bob (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)) 0=
      columnEffect (rows P) (bobNames R) r 0 := by
  change (measurements R).bob _ _=_
  rw [measurements,honest_B_effect,RowScalar.decode_qb]
  exact column_effect (preGame P) (rows P) (bobNames R) (bobNames_projective R) r 0 0 rfl

theorem reference_transport (d e : ℕ) [NeZero d] [NeZero e] (he : d=e) :
    matrixOp d (uniformBlocks d)=matrixOp e (zeroReference e) := by
  subst e
  rfl

theorem alice_reference {P : Presentation} (R : StructuralRealization P) :
    (finalStrategy R).measurements.alice (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P))) 0=
      matrixOp (RowSlots.dimension (rows P)) (zeroReference (RowSlots.dimension (rows P))) := by
  change (measurements R).alice _ _=_
  rw [measurements,honest_A_effect,RowScalar.decode_qa]
  change (newPartition (preGame P) (rows P) (aliceNames R) (aliceNames_projective R) (.global true)).effect 0=_
  refine (globalX_effect (preGame P) (rows P) (aliceNames R) (aliceNames_projective R) 0 0 rfl).trans ?_
  change matrixOp _ ((fourierPartition _).effect 0)=_
  rw [fourier_zero_uniform]
  exact reference_transport _ _ (RowScalar.dimension_bits (rows P)).symm

theorem bob_reference {P : Presentation} (R : StructuralRealization P) :
    (finalStrategy R).measurements.bob (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P))) 0=
      matrixOp (RowSlots.dimension (rows P)) (zeroReference (RowSlots.dimension (rows P))) := by
  change (measurements R).bob _ _=_
  rw [measurements,honest_B_effect,RowScalar.decode_qb]
  change (newPartition (preGame P) (rows P) (bobNames R) (bobNames_projective R) (.global true)).effect 0=_
  refine (globalX_effect (preGame P) (rows P) (bobNames R) (bobNames_projective R) 0 0 rfl).trans ?_
  change matrixOp _ ((fourierPartition _).effect 0)=_
  rw [fourier_zero_uniform]
  exact reference_transport _ _ (RowScalar.dimension_bits (rows P)).symm

/-- Exact HonestRow data on every row, including every application row, for an
 arbitrary structural realization; no application residual is assumed zero. -/
theorem honestRow {P : Presentation} (R : StructuralRealization P) (r : Fin (rows P).rowCount) :
    HonestRow (RowSlots.dimension (rows P)) (strategy R) (finalStrategy R) (density R.density)
      (slotFamily (rows P) (aliceNames R) r)
      (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
      (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P)))
      (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)) := by
  refine ⟨CompilerHonestState.marginalA _ _,fun _ => rfl,fun _ _ => rfl,
    slotFamily_unitary _ _ (aliceNames_projective R) r,
    alice_column R r,alice_reference R,bob_reference R,?_⟩
  intro k hk
  rw [bob_column]
  change right (columnEffect (rows P) (bobNames R) r 0)
      (entangle _ ((strategy R).vector k))=_
  rw [← columnEffect_mirror (rows P) (aliceNames R) (bobNames R)
    (aliceNames_projective R) (bobNames_projective R) _ (fun i => names_mirror R i k) r 0]
  exact congrArg (fun A : Op => left A (entangle _ ((strategy R).vector k)))
    (congrArg (matrixOp _) (rowColumn_zero (rows P) (aliceNames R) r))

theorem finalStrategy_finite_entropy {P : Presentation} (R : StructuralRealization P)
    (hh : FiniteDensityEntropy R.density) : FiniteMarginalEntropy (finalStrategy R) :=
  withMeasurements_entropy _ _ _ (CompilerHonestEntropyCorrect.strategy_finite_entropy R hh)


#print axioms honestRow
end Sigma2.CompilerHonestFinalCorrect
