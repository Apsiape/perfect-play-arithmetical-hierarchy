import Sigma2.CompilerSpecification
import Sigma2.Reduction

noncomputable section
namespace Sigma2.CompiledReduction
open Sigma2.Tree Sigma2.Reduction

def gameCode (f : ℕ → ℕ) (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) : ℕ :=
  f (Encodable.encode (inputPresentation R hR e))

theorem gameCode_computable {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f)
    (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) : Computable (gameCode f R hR) :=
  hC.1.comp (presentation_codes_computable R hR)

theorem gameCode_compiled {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f)
    (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) :
    Compiler.Compiled (inputPresentation R hR e) (gameCode f R hR e) :=
  CompilerSpecification.compileCode_correct hC _ (application_admissible _)

theorem theorem_7_1_reduction {f : ℕ → ℕ} (hC : CompilerSpecification.Specification f) (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) :
    (SpatialPerfect (gameCode f R hR e) ↔ ∃ n, ∀ t, R (e,n,t)=true) ∧
    (EntropyPerfect (gameCode f R hR e) ↔ ∃ n, ∀ t, R (e,n,t)=true) ∧
    ¬ FinitePerfect (gameCode f R hR e) := by
  obtain ⟨G,hG,hsp,hen,hfin,_⟩ := gameCode_compiled hC R hR e
  have hdecode (P : Game → Prop) : GameProperty P (gameCode f R hR e) ↔ P G := by
    constructor
    · rintro ⟨G',hG',hp⟩; have heq : G'=G := Option.some.inj (hG'.symm.trans hG); simpa [heq] using hp
    · intro hp; exact ⟨G,hG,hp⟩
  have hs : HasPerfect G ↔ ∃ n, ∀ t, R (e,n,t)=true := by
    rw [hsp]
    exact ⟨fun ⟨A⟩ => realization_sound R hR e A,
      fun ⟨n,hn⟩ => let ⟨A,_⟩ := realization_complete R hR e n hn; ⟨A⟩⟩
  have he : HasFiniteEntropyPerfect G ↔ ∃ n, ∀ t, R (e,n,t)=true := by
    rw [hen]
    exact ⟨fun ⟨A,_⟩ => realization_sound R hR e A,
      fun ⟨n,hn⟩ => realization_complete R hR e n hn⟩
  refine ⟨(hdecode HasPerfect).trans hs,(hdecode HasFiniteEntropyPerfect).trans he,?_⟩
  intro h
  obtain ⟨A,hA⟩ := hfin ((hdecode HasFinitePerfect).mp h)
  exact Tree.no_finite_realization (application_admissible _) A hA


end Sigma2.CompiledReduction
