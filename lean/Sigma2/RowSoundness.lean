import Sigma2.RowRestriction
import Sigma2.RowScalarGlobal

noncomputable section
namespace Sigma2.RowSoundness
open Compiler RowGame Preliminaries

/-- The component-mirror clause of RowsHold, for the concrete old-strategy
restriction. Each positive-weight original component is used; no unrelated
purification or separately chosen strategy appears in the conclusion.
This is compiler.tex (N5) and the synchronization premise of Lemma 4.3. -/
theorem component_mirrors (G : Game) (R : Rows G.scenario)
    (T : NormalStrategy (scenario G R)) (hT : Perfect (game G R) T)
    (i : Fin R.count) (k : ℕ) (hk : 0<(RowRestriction.restrict G R T).weight k) :
    (RowRestriction.restrict G R T).measurements.left (R.event i).x (R.event i).a
        ((RowRestriction.restrict G R T).vector k)=
      (RowRestriction.restrict G R T).measurements.right (R.event i).y (R.event i).b
        ((RowRestriction.restrict G R T).vector k) := by
  have hU := fact_2_1_pure_components (game G R) T hT k hk
  let V : PureStrategy G.scenario :=
    ⟨(RowRestriction.restrict G R (normalOfPure (T.component k))).measurements,T.vector k,T.unit k⟩
  have hs : BinaryEventSynchronized (normalOfPure V) (R.event i) :=
    RowRestriction.synchronized G R (normalOfPure (T.component k)) hU i
  obtain ⟨hA,_,hmA,_⟩ := marginals_exist (normalOfPure V)
  obtain ⟨P,hP⟩ := support_exists hA
  exact (RowSynchronization.pure_binary_analysis V (R.event i) hA hmA P hP hs).1

#print axioms component_mirrors
end Sigma2.RowSoundness
