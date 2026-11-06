import Sigma2.CompilerEffectivePreGame
noncomputable section
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList fmsBinding
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.cond
variable {α : Type} [Primcodable α]

@[fun_prop] theorem cfmsBinding (alice : α → Bool) (g x : α → ℕ) (p : α → ProjectionName) (a b : α → ℕ)
    (h0 : Computable alice) (h1 : Computable g) (h2 : Computable x)
    (h3 : Computable p) (h4 : Computable a) (h5 : Computable b) :
    Computable (fun z => fmsBinding (alice z) (g z) (x z) (p z) (a z) (b z)) := by
  unfold fmsBinding
  simp only [← Bool.cond_decide,bool_decide_and,bool_decide_or,bool_decide_iff]
  fun_prop

theorem fmsBinding_computable : Computable (fun z : Bool × ℕ × ℕ × ProjectionName × ℕ × ℕ =>
    fmsBinding z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) := by
  apply cfmsBinding <;> fun_prop

#print axioms cfmsBinding
#print axioms fmsBinding_computable
end Sigma2.CompilerEffectiveCoding