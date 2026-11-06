import Sigma2.CompilerEffectiveRowAccept
noncomputable section
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective
attribute [local irreducible] Nat.pair Encodable.encodeList names rowList encodingCount
  refinementCount scenario rows preGame finalGame RowGame.questions
  RowSlots.raw RowSlots.bound RowSlots.squares RowSlots.dimension
  questionsNat dimensionNat decodedPresentation
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair

theorem decodedPresentation_computable : Computable decodedPresentation := by
  unfold decodedPresentation
  exact
  Primrec.option_getD.to_comp.comp presentation_decoder_computable (Computable.const emptyPresentation)

theorem questionsNat_length (P : Presentation) :
    (questionsNat P).length=(RowGame.questions (rows P)).length := by
  rw [questionsNat_eq,List.length_map]

theorem final_questionsA_eq (P : Presentation) :
    (finalGame P).scenario.questionsA=(scenario P).questionsA+(questionsNat P).length := by
  unfold finalGame RowGame.game RowGame.scenario preGame
  change (scenario P).questionsA+(RowGame.questions (rows P)).length=_
  rw [questionsNat_length]

theorem final_questionsB_eq (P : Presentation) :
    (finalGame P).scenario.questionsB=(scenario P).questionsA+(questionsNat P).length := by
  unfold finalGame RowGame.game RowGame.scenario preGame
  change (scenario P).questionsB+(RowGame.questions (rows P)).length=_
  rw [pre_counts_eq,questionsNat_length]

theorem final_answersA_eq (P : Presentation) :
    (finalGame P).scenario.answersA=11+11+2*dimensionNat P+6 := by
  have ha : (scenario P).answersA=11 := by unfold scenario; rfl
  have hb : (scenario P).answersB=11 := by unfold scenario; rfl
  unfold finalGame RowGame.game RowGame.scenario preGame
  change (scenario P).answersA+(scenario P).answersB+2*RowSlots.dimension (rows P)+6=_
  exact congrArg₂ (fun (v d : ℕ) => v+2*d+6) (congrArg₂ Nat.add ha hb) (dimensionNat_eq P).symm

theorem final_answersB_eq (P : Presentation) :
    (finalGame P).scenario.answersB=11+11+2*dimensionNat P+6 := by
  have ha : (scenario P).answersA=11 := by unfold scenario; rfl
  have hb : (scenario P).answersB=11 := by unfold scenario; rfl
  unfold finalGame RowGame.game RowGame.scenario preGame
  change (scenario P).answersA+(scenario P).answersB+2*RowSlots.dimension (rows P)+6=_
  exact congrArg₂ (fun (v d : ℕ) => v+2*d+6) (congrArg₂ Nat.add ha hb) (dimensionNat_eq P).symm

theorem final_questionsA_computable : Computable (fun P : Presentation => (finalGame P).scenario.questionsA) := by
  have hq := pre_count_computable
  have hc : Computable (fun P : Presentation => (scenario P).questionsA+(questionsNat P).length) := by fun_prop
  exact hc.of_eq (fun P => (final_questionsA_eq P).symm)

theorem final_questionsB_computable : Computable (fun P : Presentation => (finalGame P).scenario.questionsB) := by
  exact final_questionsA_computable.of_eq (fun P => (final_questionsA_eq P).trans (final_questionsB_eq P).symm)

theorem final_answersA_computable : Computable (fun P : Presentation => (finalGame P).scenario.answersA) := by
  have hc : Computable (fun P : Presentation => 11+11+2*dimensionNat P+6) := by fun_prop
  exact hc.of_eq (fun P => (final_answersA_eq P).symm)

theorem final_answersB_computable : Computable (fun P : Presentation => (finalGame P).scenario.answersB) := by
  exact final_answersA_computable.of_eq (fun P => (final_answersA_eq P).trans (final_answersB_eq P).symm)

def scenarioFamily (n : ℕ) : Scenario := (finalGame (decodedPresentation n)).scenario
attribute [local irreducible] scenarioFamily

theorem family_questionsA_computable : Computable (fun n => (scenarioFamily n).questionsA) :=
  by
    unfold scenarioFamily
    exact final_questionsA_computable.comp decodedPresentation_computable

theorem family_questionsB_computable : Computable (fun n => (scenarioFamily n).questionsB) :=
  by
    unfold scenarioFamily
    exact final_questionsB_computable.comp decodedPresentation_computable

theorem family_answersA_computable : Computable (fun n => (scenarioFamily n).answersA) :=
  by
    unfold scenarioFamily
    exact final_answersA_computable.comp decodedPresentation_computable

theorem family_answersB_computable : Computable (fun n => (scenarioFamily n).answersB) :=
  by
    unfold scenarioFamily
    exact final_answersB_computable.comp decodedPresentation_computable

#print axioms final_questionsA_computable
#print axioms final_questionsB_computable
#print axioms final_answersA_computable
#print axioms family_questionsA_computable
end Sigma2.CompilerEffectiveCoding