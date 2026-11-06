import Sigma2.CompilerApproxRejection
import Sigma2.CompilerApproxDictionaryEvents

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
namespace Sigma2.CompilerApproxDictionaryStrategy
open Compiler CompilerScaffold CompilerEventLoss CompilerEventCounting CompilerEvents CompilerEventState
  CompilerEventSlots CompilerApproxRows CompilerApproxRejection CompilerApproxDictionaryIndex
  CompilerApproxDictionaryEnergy CompilerApproxDictionaryBound RowCompleteness RowGame RowColumns FiniteAncilla TensorLifts

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

/-- The unchanged frozen measurements, with the unchanged entangled ensemble. -/
def extension (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) :
    NormalStrategy (scenario G R) :=
  withMeasurements (RowSlots.dimension R) S (honestMeasurements G R S.measurements E F hE hF)

/-- Every HonestRow field holds at the actual column/reference question indices.
No row-zero equation, perfection or approximation hypothesis is used. -/
theorem honest_row (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (h : Density) (hmarg : MarginalA S h)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i))
    (hm : ∀ i k,0<S.weight k → left (E i) (S.vector k)=right (F i) (S.vector k))
    (r : Fin R.rowCount) :
    HonestRow (RowSlots.dimension R) S (extension G R S E F hE hF) h (slotFamily R E r)
      (RowScalar.qa G R (columnQuestion R r)) (RowScalar.qa G R (referenceQuestion R))
      (RowScalar.qb G R (referenceQuestion R)) (RowScalar.qb G R (columnQuestion R r)) := by
  refine ⟨hmarg,fun _ => rfl,fun _ _ => rfl,slotFamily_unitary R E hE r,?_,?_,?_,?_⟩
  · change (honestMeasurements G R S.measurements E F hE hF).alice _ 0=_
    rw [honest_A_effect,RowScalar.decode_qa]
    change (newPartition G R E hE (.column r)).effect 0=_
    rw [column_effect G R E hE r 0 0 rfl]
    exact congrArg (matrixOp (RowSlots.dimension R)) (rowColumn_zero R E r)
  · change (honestMeasurements G R S.measurements E F hE hF).alice _ 0=_
    rw [honest_A_effect,RowScalar.decode_qa]
    change (newPartition G R E hE (.global true)).effect 0=_
    rw [globalX_effect G R E hE 0 0 rfl]
    change matrixOp _ ((fourierPartition (bits R)).effect 0)=_
    rw [fourier_zero_uniform,uniform_dimension (bits R) (RowSlots.dimension R) (RowScalar.dimension_bits R)]
    rfl
  · change (honestMeasurements G R S.measurements E F hE hF).bob _ 0=_
    rw [honest_B_effect,RowScalar.decode_qb]
    change (newPartition G R F hF (.global true)).effect 0=_
    rw [globalX_effect G R F hF 0 0 rfl]
    change matrixOp _ ((fourierPartition (bits R)).effect 0)=_
    rw [fourier_zero_uniform,uniform_dimension (bits R) (RowSlots.dimension R) (RowScalar.dimension_bits R)]
    rfl
  · intro k hk
    change right ((honestMeasurements G R S.measurements E F hE hF).bob _ 0)
      (entangle (RowSlots.dimension R) (S.vector k))=_
    rw [honest_B_effect,RowScalar.decode_qb]
    change right ((newPartition G R F hF (.column r)).effect 0) _=_
    rw [column_effect G R F hF r 0 0 rfl,← rowColumn_zero R E r]
    exact (columnEffect_mirror R E F hE hF (S.vector k)
      (fun i => hm i k (lt_of_le_of_ne (S.weight_nonneg k) (Ne.symm hk))) r 0).symm

/-- The named projection dictionary agrees on every occupied base vector.
The extension itself uses numbered R globally, including off the state support. -/
def NamedProjections (P : Presentation) (R : StructuralRealization P)
    (S : NormalStrategy (preGame P).scenario) : Prop :=
  ∀ i k,0<S.weight k → left (numbered R i) (S.vector k)=
    S.measurements.left ((rows P).event i).x ((rows P).event i).a (S.vector k)

/-- Literal equality of the original named effects is a sufficient stronger input. -/
theorem namedProjections_of_effects (P : Presentation) (R : StructuralRealization P)
    (S : NormalStrategy (preGame P).scenario)
    (h : ∀ i,S.measurements.alice ((rows P).event i).x ((rows P).event i).a=numbered R i) :
    NamedProjections P R S := by
  intro i k hk
  rw [measurements_left,h i]

/-- Alice uses the literal global numbered projections. Bob uses the frozen
support-compressed named projections; their occupied actions synchronize. -/
theorem honest_extension (P : Presentation) (R : StructuralRealization P)
    (S : NormalStrategy (preGame P).scenario) (hS : Perfect (preGame P) S)
    (hR : StructuralRowsHold P S) (hN : NamedBinaryProjections (rows P) S)
    (hmarg : MarginalA S (oldDensity R))
    (hnamed : NamedProjections P R S) :
    ∃ T : NormalStrategy (finalGame P).scenario,
      HonestApplicationRows P R T ∧ classContribution P T .structural=0 ∧
      classContribution P T .preGame=0 := by
  obtain ⟨E,F,hE,hF,he,hf,hm⟩ := compressed_named_on (preGame P) (rows P) S
    (fun r => ¬ applicationRow P r) hR hN
  have he' : ∀ i k,0<S.weight k → left (numbered R i) (S.vector k)=
      S.measurements.left ((rows P).event i).x ((rows P).event i).a (S.vector k) := hnamed
  have hm' : ∀ i k,0<S.weight k → left (numbered R i) (S.vector k)=right (F i) (S.vector k) :=
    fun i k hk => (he' i k hk).trans ((he i k hk).symm.trans (hm i k hk))
  refine ⟨extension (preGame P) (rows P) S (numbered R) F (numbered_projection R) hF,?_,?_,?_⟩
  · refine ⟨(preGame P).scenario,S,?_⟩
    intro j
    exact honest_row (preGame P) (rows P) S (oldDensity R) hmarg
      (numbered R) F (numbered_projection R) hF hm' (rowIndex P j)
  · exact honest_class_zero P S hS hR hN (numbered R) F (numbered_projection R) hF he' hf hm'
      .structural (Or.inl rfl)
  · exact honest_class_zero P S hS hR hN (numbered R) F (numbered_projection R) hF he' hf hm'
      .preGame (Or.inr rfl)

end Sigma2.CompilerApproxDictionaryStrategy
