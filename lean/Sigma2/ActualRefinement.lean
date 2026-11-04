import Sigma2.RefinementSigns
import Sigma2.RefinementLabel
noncomputable section
open scoped BigOperators
namespace Sigma2.ActualRefinement
open Compiler Preliminaries BridgeRefinementTransfer RefinementCoarse

theorem pure_refinement {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (hA hB : Density) (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    RefinementConclusion (normalOfPure S) I F P Q := by
  have ha := RefinementSigns.alice_signs S I F hF hA hB hmA hmB P Q hP hQ
  have hb := RefinementSigns.bob_signs S I F hF hA hB hmA hmB P Q hP hQ
  refine ⟨ha,hb,?_,?_⟩
  · intro a
    have hc := RefinementLabel.alice_label S I F hF hA hmA P hP a
    rwa [ha a] at hc
  · intro b
    have hc := RefinementLabel.bob_label S I F hF hB hmB Q hQ b
    rwa [hb b] at hc

theorem actual_refinement {s} (S : NormalStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect S I F)
    (hA hB : Density) (mA : MarginalA S hA) (mB : MarginalB S hB)
    (eA eB : Op) (sA : SupportOf hA eA) (sB : SupportOf hB eB) :
    RefinementConclusion S I F eA eB := by
  exact refinement_pure_transfer S I F hF hA hB mA mB eA eB sA sB
    (fun T hT kA kB mkA mkB pA pB spA spB => pure_refinement T I F hT kA kB mkA mkB pA pB spA spB)

/-- The flag-to-magic block of the common sign commutator is the prescribed
transport identity beta P_f = P_m beta; no independent bridge is chosen. -/
theorem block_transport (f m X L : Op) (hf : Projection f) (hm : Projection m)
    (hfL : f*L=L*f) (hmL : m*L=L*m) (hXL : X*L=L*X) :
    (m*X*f)*(f*L*f)=(m*L*m)*(m*X*f) := by
  have hl : (m*X*f)*(f*L*f)=m*L*X*f := by
    calc
      _=m*X*(f*f)*L*f := by noncomm_ring
      _=m*X*(f*L)*f := by rw [hf.2]; noncomm_ring
      _=m*X*(L*f)*f := by rw [hfL]
      _=m*(X*L)*(f*f) := by noncomm_ring
      _=m*(L*X)*f := by rw [hXL,hf.2]
      _=_ := by noncomm_ring
  have hr : (m*L*m)*(m*X*f)=m*L*X*f := by
    calc
      _=m*L*(m*m)*X*f := by noncomm_ring
      _=m*(L*m)*X*f := by rw [hm.2]; noncomm_ring
      _=m*(m*L)*X*f := by rw [← hmL]
      _=(m*m)*L*X*f := by noncomm_ring
      _=_ := by rw [hm.2]
  exact hl.trans hr.symm

#print axioms block_transport
#print axioms pure_refinement
#print axioms actual_refinement
end Sigma2.ActualRefinement
