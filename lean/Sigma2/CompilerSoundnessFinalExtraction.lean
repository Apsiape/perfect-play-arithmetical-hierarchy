import Sigma2.CompilerSoundnessSourceOperators

/-! Extraction preserving the actual final ensemble and binary event. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessFinalExtraction
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessSupport CompilerSoundnessPadding CompilerSoundnessRows Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def sourceQuestion (P : Presentation) : QA (finalGame P).scenario :=
  (RowGame.embedding (preGame P) (rows P)).qA
    (namedEvent P (.parameter 0) (CompilerSoundnessBindings.parameter_mem P 0 (by omega))).x

def sourceAnswer (P : Presentation) : AA (finalGame P).scenario :=
  (RowGame.embedding (preGame P) (rows P)).aA 1

theorem finite_sum_single {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → Op) (a : ι) :
    (∑ b,if b=a then A b else 0)=A a := by simp

theorem restriction_one (P : Presentation) (T : NormalStrategy (finalGame P).scenario)
    (x : QA (scenario P)) :
    (RowRestriction.restrict (preGame P) (rows P) T).measurements.alice x 1=
      T.measurements.alice ((RowGame.embedding (preGame P) (rows P)).qA x) (sourceAnswer P) := by
  change (∑ aa,if RowRestriction.foldA (preGame P) (rows P) aa=1 then
    T.measurements.alice ((RowGame.embedding (preGame P) (rows P)).qA x) aa else 0)=_
  have hf (aa : AA (finalGame P).scenario) :
      RowRestriction.foldA (preGame P) (rows P) aa=1 ↔ aa=sourceAnswer P := by
    constructor
    · intro hh
      have hv := congrArg Fin.val hh
      by_cases ha : aa.val<(preGame P).scenario.answersA+1
      · simp only [RowRestriction.foldA,ha,dite_true] at hv
        apply Fin.ext
        change aa.val=1 at hv ⊢
        exact hv
      · simp only [RowRestriction.foldA,ha,dite_false] at hv
        change (0:ℕ)=1 at hv
        omega
    · intro hh
      subst aa
      rfl
  simp_rw [hf]
  exact finite_sum_single _ _

theorem of_final (P : Presentation) (T : NormalStrategy (finalGame P).scenario)
    (hT : Perfect (finalGame P) T) :
    ∃ E : SupportedScaffold P,
      E.strategy.vector=T.vector ∧ E.strategy.weight=T.weight ∧
      CompilerSoundnessSource.support E=
        E.supportA*T.measurements.alice (sourceQuestion P) (sourceAnswer P)*E.supportA := by
  let U := RowRestriction.restrict (preGame P) (rows P) T
  have hU := RowSoundness.soundness (preGame P) (rows P) T hT
  let S := normalize P U
  have hS : Perfect (preGame P) S := perfect P U hU.1
  have hR : RowsHold (rows P) S := rowsHold P U hU.1 hU.2.2.1
  obtain ⟨hA,hB,eA,eB,hmA,hmB,heA,heB,hrA,hrB⟩ := decoded_rows P S hR
  let E : SupportedScaffold P := ⟨S,hS,hA,hB,eA,eB,hmA,hmB,heA,heB,hR,hrA,hrB,conditionalPerfect P U hU.1⟩
  refine ⟨E,rfl,rfl,?_⟩
  change projectionA P S eA (.parameter 0)=_
  rw [projectionA_of_mem P S eA _ (CompilerSoundnessBindings.parameter_mem P 0 (by omega))]
  rw [show S.measurements.alice (namedEvent P (.parameter 0) (CompilerSoundnessBindings.parameter_mem P 0 (by omega))).x 1=
      U.measurements.alice (namedEvent P (.parameter 0) (CompilerSoundnessBindings.parameter_mem P 0 (by omega))).x 1 from
    binary_alice P U _ 1]
  rw [restriction_one]
  rfl

theorem marginal_preserved {s t : Scenario} (S : NormalStrategy s) (T : NormalStrategy t)
    (hv : S.vector=T.vector) (hw : S.weight=T.weight) (h : Density) :
    MarginalA S h ↔ MarginalA T h := by
  unfold MarginalA
  rw [hv,hw]

#print axioms of_final
end Sigma2.CompilerSoundnessFinalExtraction
