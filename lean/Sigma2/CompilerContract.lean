import Sigma2.CompilerEffectiveCoding

/-! The final compiler interface. These are open propositions, not axioms. -/
noncomputable section
namespace Sigma2.CompilerContract
open Compiler CompilerScaffold Preliminaries

def Soundness (P : Presentation) : Prop :=
  HasPerfect (finalGame P) → Nonempty (NormalRealization P)

def FiniteEntropySoundness (P : Presentation) : Prop :=
  HasFiniteEntropyPerfect (finalGame P) →
    ∃ R : NormalRealization P, RealizationFiniteEntropy R

def FiniteSupportSoundness (P : Presentation) : Prop :=
  HasFinitePerfect (finalGame P) →
    ∃ R : NormalRealization P, FiniteRealization R

def SourceEventSoundness (P : Presentation) : Prop :=
  ∃ (x : QA (finalGame P).scenario) (a : AA (finalGame P).scenario),
    ∀ S, Perfect (finalGame P) S →
      ∃ (R : NormalRealization P) (h : Density) (e : Op),
        MarginalA S h ∧ SupportOf h e ∧
        R.support=e*S.measurements.alice x a*e ∧
        R.density.op=(121:ℂ) • (R.support*h.op*R.support) ∧
        (trace (h.op*R.support)).re=1/121

def Completeness (P : Presentation) : Prop :=
  Nonempty (NormalRealization P) → HasPerfect (finalGame P)

def FiniteEntropyCompleteness (P : Presentation) : Prop :=
  (∃ R : NormalRealization P, RealizationFiniteEntropy R) →
    HasFiniteEntropyPerfect (finalGame P)

def Approximation (P : Presentation) : Prop := ApproxCompiled P (codeFor P)

def Obligations (P : Presentation) : Prop :=
  Soundness P ∧ FiniteEntropySoundness P ∧ FiniteSupportSoundness P ∧
    SourceEventSoundness P ∧ Completeness P ∧ FiniteEntropyCompleteness P ∧ Approximation P

theorem compiled_of_obligations (P : Presentation) (h : Obligations P) :
    Compiled P (codeFor P) := by
  rcases h with ⟨hs,he,hf,hsrc,hc,hec,_⟩
  exact ⟨finalGame P,decode_codeFor P,⟨hs,hc⟩,⟨he,hec⟩,hf,hsrc⟩

/-- Lemma 4.5 at four bridges, assembled from the seven compiler obligations. -/
theorem lemma_4_4_strong_of_obligations
    (h : ∀ P : Presentation, P.admissible → Obligations P) :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ code P,
      Encodable.decode (α := Presentation) code=some P → P.admissible →
        Compiled P (f code) ∧ ApproxCompiled P (f code) := by
  refine ⟨codeMap,CompilerEffectiveCoding.codeMap_computable,?_⟩
  intro code P hd hp
  have hc : codeMap code=codeFor P := by simp only [codeMap,hd]
  rw [hc]
  exact ⟨compiled_of_obligations P (h P hp),(h P hp).2.2.2.2.2.2⟩

#print axioms compiled_of_obligations
#print axioms lemma_4_4_strong_of_obligations
end Sigma2.CompilerContract
