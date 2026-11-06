import Sigma2.ReductionPresentation

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace Sigma2.ReductionSoundBridge
open Sigma2.Tree Sigma2.Reduction

/-- The proved finite clock sector and definite tableau force a globally
nonrejecting pulse period. No concrete presentation-row extraction is assumed
by the original reduction theorem; that extraction remains a separate task. -/
theorem nonreject_of_data {P : Presentation} (hP : P.admissible)
    (A : NormalRealization P) (C : Coordinates A) (M : Automaton) (T : Tableau A C M)
    (D : Clock.Data A) (hpulse : T.pulse=D.pulse) :
    ∃ q, 0<q ∧ ∀ t x, run M (fun y => decide (q ∣ y)) t x≠2 := by
  obtain ⟨q,ζ,ξ,hζ,hξ,hroot,heig⟩ := Clock.finite_phase_sector hP A D
  have hp (w : Word) : T.pulse (wordOp A w ξ)=
      if (fun y => decide (q ∣ y)) (yCoord w) then wordOp A w ξ else 0 := by
    rw [hpulse,Clock.exact_return hP A D q ζ hζ ξ hroot heig w]
    simp only [decide_eq_true_eq]
  have htab := lemma_5_1_definite_computation hP A C M T
    (fun y => decide (q ∣ y)) ξ hroot hp
  have hfix : A.support ξ=ξ := by
    rw [← hroot]
    exact congrArg (fun L : Op => L ξ) (A.label_supported P.root).1
  have hpow (n : ℕ) : n<2^n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ]; omega
  refine ⟨q,hζ.1,?_⟩
  intro t x ht
  let n := x+t+1
  have hx : x<2^n := lt_trans (by dsimp [n]; omega) (hpow n)
  have hy : t<2^n := lt_trans (by dsimp [n]; omega) (hpow n)
  obtain ⟨w,_,hwx,hwy⟩ := word_of_coords n x t hx hy
  have ha := htab w 2
  rw [hwx,hwy,ht,if_pos rfl,T.no_halt] at ha
  have hz : wordOp A w ξ=0 := by simpa using ha.symm
  have hi := congrArg (fun L : Op => L ξ) (word_isometry A w)
  simp only [mul_apply_eq_comp,hz,map_zero,hfix] at hi
  exact hξ hi.symm

/-- After the concrete rows produce the three structures, the remaining
logical implication in realization_sound is checked against the actual
programCode and its closed effective_program specification. -/
theorem sound_of_data (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ)
    (A : NormalRealization (inputPresentation R hR e))
    (C : Coordinates A)
    (T : Tableau A C (decodeAutomaton (programCode R hR e)))
    (D : Clock.Data A) (hpulse : T.pulse=D.pulse) : ∃ n, ∀ t, R (e,n,t)=true := by
  obtain ⟨q,hq,hno⟩ := nonreject_of_data (application_admissible _) A C _ T D hpulse
  have hc : ProgramCorrect R e (decodeAutomaton (programCode R hR e)) :=
    (Classical.choose_spec (effective_program R hR)).2 e
  obtain ⟨n,_,hn⟩ := (hc.1 q hq).mp hno
  exact ⟨n,hn⟩

#print axioms nonreject_of_data
#print axioms sound_of_data
end Sigma2.ReductionSoundBridge
