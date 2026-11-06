import Sigma2.CompilerEffectiveTable
/-! Unconditional computability of the frozen concrete compiler map.
All decoders, counts, entries, and table ordering are discharged below. -/
noncomputable section
namespace Sigma2.CompilerEffectiveCoding

theorem expr_codec_unchanged : exprPrimcodable.toEncodable=Sigma2.instEncodableExpr := rfl

theorem label_codec_unchanged : labelPrimcodable.toEncodable=Sigma2.instEncodableLabelType := rfl

theorem presentation_codec_unchanged : presentationPrimcodable.toEncodable=Sigma2.instEncodablePresentation := rfl

/-- No generator, validity, or serialization premises remain. -/
theorem codeMap_computable : Computable Sigma2.CompilerScaffold.codeMap :=
  CompilerEffective.codeMap_computable_of_uniform scenarioFamily distributionFamily acceptanceFamily
    family_questionsA_computable family_questionsB_computable
    family_answersA_computable family_answersB_computable
    distributionFamily_computable acceptanceFamily_computable
    presentation_validity_computable rawFamily_eq_of_decode

#check @codeMap_computable
#print axioms codeMap_computable
#print axioms expr_codec_unchanged
#print axioms label_codec_unchanged
#print axioms presentation_codec_unchanged
end Sigma2.CompilerEffectiveCoding