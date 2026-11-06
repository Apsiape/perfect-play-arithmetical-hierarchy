import Sigma2.CompilerBase

/-! The frozen strong compiler's content, parameterized by its function. -/
noncomputable section
namespace Sigma2.CompilerSpecification
open Compiler

def Specification (f : ℕ → ℕ) : Prop :=
  Computable f ∧ ∀ code P,
    Encodable.decode (α := Presentation) code = some P → P.admissible →
      Compiled P (f code) ∧ ApproxCompiled P (f code)

theorem strong_compiler {f : ℕ → ℕ} (hC : Specification f) :
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ code P,
      Encodable.decode (α := Presentation) code = some P → P.admissible →
        Compiled P (g code) ∧ ApproxCompiled P (g code) := ⟨f,hC⟩

theorem four_bridge_compiler {f : ℕ → ℕ} (hC : Specification f) :
    ∃ g : ℕ → ℕ, Computable g ∧ ∀ code P,
      Encodable.decode (α := Presentation) code = some P → P.admissible →
        Compiled P (g code) := ⟨f,hC.1,fun code P hd hp => (hC.2 code P hd hp).1⟩

theorem compileCode_computable {f : ℕ → ℕ} (hC : Specification f) : Computable f := hC.1

theorem compileCode_correct {f : ℕ → ℕ} (hC : Specification f)
    (P : Presentation) (hP : P.admissible) : Compiled P (f (Encodable.encode P)) :=
  (hC.2 _ P (Encodable.encodek P) hP).1

theorem approximate_compilation {f : ℕ → ℕ} (hC : Specification f)
    (P : Presentation) (hP : P.admissible) : ApproxCompiled P (f (Encodable.encode P)) :=
  (hC.2 _ P (Encodable.encodek P) hP).2

end Sigma2.CompilerSpecification
