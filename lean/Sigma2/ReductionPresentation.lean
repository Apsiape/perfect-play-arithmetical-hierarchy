import Sigma2.PresentationSerialize

noncomputable section
namespace Sigma2.Reduction
open Sigma2.Tree

theorem presentation_codes_computable (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    Computable (fun e => Encodable.encode (inputPresentation R hR e)) := by
  have hd : Computable (fun c : ℕ =>
      (Encodable.decode (α := RawAutomaton) c).getD (0,[])) :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const (0,[]))).to_comp
  unfold inputPresentation decodeAutomaton
  exact PresentationCoding.application_code_primrec.to_comp.comp
    (hd.comp (programCode_computable R hR))

end Sigma2.Reduction

#print axioms Sigma2.Reduction.presentation_codes_computable
