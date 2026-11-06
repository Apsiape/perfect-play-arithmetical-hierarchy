import Sigma2.ReductionPresentation
import Sigma2.ReductionSoundBridge
import Sigma2.ReductionTableauRows
import Sigma2.ReductionFockRealization

noncomputable section
namespace Sigma2.Reduction
open Sigma2.Tree

/-- The soundness path is compiler -> Fock -> finite clock sector -> definite tableau. -/
theorem realization_sound (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ)
    (A : NormalRealization (inputPresentation R hR e)) :
    ∃ n, ∀ t, R (e,n,t)=true := by
  exact ReductionSoundBridge.sound_of_data R hR e A
    (ReductionRows.coordinates A) (ReductionRows.tableau A) (ReductionRows.clockData A) rfl

#print axioms realization_sound

/-- Fock/Weyl/reader/classical tableau witness, including root finite entropy. -/
theorem realization_complete (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e n : ℕ)
    (hn : ∀ t, R (e,n,t)=true) :
    ∃ A : NormalRealization (inputPresentation R hR e), RealizationFiniteEntropy A := by
  obtain ⟨q,ζ,hrank,hζ,hsep,hrun⟩ := ReductionWitnessArithmetic.prime_phase R hR e n hn
  letI : NeZero q := ⟨Nat.ne_of_gt hrank.1.pos⟩
  have hnorm : ‖ζ‖=1 := (hζ.isOfFinOrder (NeZero.ne q)).norm_eq_one
  exact ⟨ReductionFockModel.realization q (decodeAutomaton (programCode R hR e)) ζ hnorm hζ hsep hrun,
    ReductionFockModel.realization_finiteEntropy q (decodeAutomaton (programCode R hR e)) ζ hnorm hζ hsep hrun⟩

#print axioms Sigma2.Reduction.realization_complete

end Sigma2.Reduction

