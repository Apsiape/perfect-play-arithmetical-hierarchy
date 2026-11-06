import Sigma2.CompilerEffectivePreBindings
noncomputable section
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective Compiler
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList question valid
  fmsBinding refinementLabel directed rule encodingCount
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.cond
  encodingCount_computable
variable {α : Type} [Primcodable α]

@[fun_prop] theorem crefLabel (P : α → Presentation) (g k : α → ℕ)
    (hP : Computable P) (hg : Computable g) (hk : Computable k) :
    Computable (fun a => refinementLabel (P a) (g a) (k a)) := by
  unfold refinementLabel
  have he := encodingCount_computable.comp hP
  fun_prop

@[fun_prop] theorem cdirected (P : α → Presentation) (alice : α → Bool)
    (q p : α → Question) (a b : α → ℕ)
    (hP : Computable P) (hal : Computable alice) (hq : Computable q)
    (hp : Computable p) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => directed (P z) (alice z) (q z) (p z) (a z) (b z)) := by
  let F : α × (ℕ × ℕ) → Bool := fun z =>
    questionMatch (p z.1)
      (fun n => fmsBinding (alice z.1) z.2.1 z.2.2 n (a z.1) (b z.1))
      (fun _ => true) (fun _ => true) true
  have hF : Computable F :=
    cquestionMatch (fun z : α × (ℕ × ℕ) => p z.1)
      (fun z => fmsBinding (alice z.1.1) z.1.2.1 z.1.2.2 z.2 (a z.1.1) (b z.1.1))
      (fun _ => true) (fun _ => true) (fun _ => true)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  let R : α × (ℕ × ℕ) → Bool := fun z =>
    questionMatch (p z.1)
      (fun n => if n=refinementLabel (P z.1) z.2.1 z.2.2 then
        decide ((a z.1%2=1) ↔ b z.1=1) else true)
      (fun hy => if z.2.1=hy.1 ∧ hy.2 ∈ [0,3,4] then
        if alice z.1 then conditionalFmsRule 3 hy.2 (a z.1/2) (b z.1)
        else conditionalFmsRule hy.2 3 (b z.1) (a z.1/2) else true)
      (fun _ => true) true
  have hR : Computable R := by
    apply cquestionMatch (fun z : α × (ℕ × ℕ) => p z.1)
      (fun z => if z.2=refinementLabel (P z.1.1) z.1.2.1 z.1.2.2 then
        decide ((a z.1.1%2=1) ↔ b z.1.1=1) else true)
      (fun z => if z.1.2.1=z.2.1 ∧ z.2.2 ∈ [0,3,4] then
        if alice z.1.1 then conditionalFmsRule 3 z.2.2 (a z.1.1/2) (b z.1.1)
        else conditionalFmsRule z.2.2 3 (b z.1.1) (a z.1.1/2) else true)
      (fun _ => true) (fun _ => true)
    · fun_prop
    · simp only [← Bool.cond_decide,bool_decide_and,bool_decide_or,bool_decide_iff]; fun_prop
    · simp only [← Bool.cond_decide,bool_decide_and,bool_decide_or,bool_decide_iff]; fun_prop
    · fun_prop
    · fun_prop
  have hc := cquestionMatch q (fun _ => true) F R (fun _ => true)
    hq (Computable.const true) hF hR (Computable.const true)
  exact hc.of_eq (fun z => by
    cases hqz : q z <;> cases hpz : p z <;>
      simp only [F,R,questionMatch,CompilerScaffold.directed,hqz,hpz])


theorem directed_computable : Computable (fun z : Presentation × Bool × Question × Question × ℕ × ℕ =>
    directed z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) := by
  apply cdirected <;> fun_prop

@[fun_prop] theorem crule (P : α → Presentation) (q p : α → Question) (a b : α → ℕ)
    (hP : Computable P) (hq : Computable q) (hp : Computable p)
    (ha : Computable a) (hb : Computable b) :
    Computable (fun z => rule (P z) (q z) (p z) (a z) (b z)) := by
  let B : α × ProjectionName → Bool := fun z =>
    questionMatch (p z.1) (fun m => if z.2=m then decide (a z.1=b z.1) else true)
      (fun _ => true) (fun _ => true) true
  have hB : Computable B :=
    cquestionMatch (fun z : α × ProjectionName => p z.1)
      (fun z => if z.1.2=z.2 then decide (a z.1.1=b z.1.1) else true)
      (fun _ => true) (fun _ => true) (fun _ => true)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  let F : α × (ℕ × ℕ) → Bool := fun z =>
    questionMatch (p z.1) (fun _ => true)
      (fun hy => if z.2.1=hy.1 then conditionalFmsRule z.2.2 hy.2 (a z.1) (b z.1) else true)
      (fun _ => true) true
  have hF : Computable F :=
    cquestionMatch (fun z : α × (ℕ × ℕ) => p z.1) (fun _ => true)
      (fun z => if z.1.2.1=z.2.1 then conditionalFmsRule z.1.2.2 z.2.2 (a z.1.1) (b z.1.1) else true)
      (fun _ => true) (fun _ => true)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  let middle : α → Bool := fun z => questionMatch (q z) (fun n => B (z,n))
    (fun gx => F (z,gx)) (fun _ => true) true
  have hm : Computable middle := cquestionMatch q B F (fun _ => true) (fun _ => true)
    hq hB hF (Computable.const true) (Computable.const true)
  have hc : Computable (fun z => valid (q z) (a z) && valid (p z) (b z) && middle z &&
      directed (P z) true (q z) (p z) (a z) (b z) &&
      directed (P z) false (p z) (q z) (b z) (a z)) := by fun_prop
  exact hc.of_eq (fun z => by
    cases hqz : q z <;> cases hpz : p z <;>
      simp only [middle,B,F,questionMatch,CompilerScaffold.rule,hqz,hpz])

theorem rule_computable : Computable (fun z : Presentation × Question × Question × ℕ × ℕ =>
    rule z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by apply crule <;> fun_prop

def preAcceptsNat (P : Presentation) (x y a b : ℕ) : Bool :=
  rule P (question P x) (question P y) a b

theorem preAcceptsNat_computable : Computable (fun z : Presentation × ℕ × ℕ × ℕ × ℕ =>
    preAcceptsNat z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
  unfold preAcceptsNat
  fun_prop

theorem preAcceptsNat_eq (P : Presentation) (x : QA (scenario P)) (y : QB (scenario P))
    (a : AA (scenario P)) (b : BB (scenario P)) :
    preAcceptsNat P x.val y.val a.val b.val=(preGame P).accepts x y a b := rfl

#print axioms directed_computable
#print axioms rule_computable
#print axioms preAcceptsNat_computable
#print axioms preAcceptsNat_eq
end Sigma2.CompilerEffectiveCoding