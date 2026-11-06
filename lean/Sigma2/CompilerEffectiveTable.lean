import Sigma2.CompilerEffectiveCounts
noncomputable section
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective GameTableEffective
attribute [local irreducible] Nat.pair Encodable.encodeList names rowList encodingCount
  refinementCount scenario rows preGame finalGame RowGame.questions
  RowSlots.raw RowSlots.bound RowSlots.squares RowSlots.dimension
  questionsNat dimensionNat decodedPresentation scenarioFamily acceptsRowNat
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair

def distributionFamily (n k : ℕ) : ℚ :=
  1 / (((scenarioFamily n).questionsA+1)*((scenarioFamily n).questionsB+1) : ℕ)

def acceptanceFamily (n k : ℕ) : Bool :=
  let B := (scenarioFamily n).questionsB+1
  let C := (scenarioFamily n).answersA+1
  let D := (scenarioFamily n).answersB+1
  let xy := k/(C*D)
  let ab := k%(C*D)
  acceptsRowNat (decodedPresentation n) (xy/B) (xy%B) (ab/D) (ab%D)
attribute [local irreducible] distributionFamily acceptanceFamily

theorem distributionFamily_computable : Computable₂ distributionFamily := by
  change Computable (fun z : ℕ × ℕ => distributionFamily z.1 z.2)
  have hqa := family_questionsA_computable.comp (Computable.fst (α := ℕ) (β := ℕ))
  have hqb := family_questionsB_computable.comp (Computable.fst (α := ℕ) (β := ℕ))
  have hc : Computable (fun z : ℕ × ℕ =>
      ((scenarioFamily z.1).questionsA+1)*((scenarioFamily z.1).questionsB+1)) := by fun_prop
  apply (UpperCoding.rat_divNat.comp ((Computable.const (1:ℤ)).pair hc)).of_eq
  intro z
  unfold distributionFamily
  simp

theorem acceptanceFamily_computable : Computable₂ acceptanceFamily := by
  change Computable (fun z : ℕ × ℕ => acceptanceFamily z.1 z.2)
  have hP := decodedPresentation_computable.comp (Computable.fst (α := ℕ) (β := ℕ))
  have hqb := family_questionsB_computable.comp (Computable.fst (α := ℕ) (β := ℕ))
  have haa := family_answersA_computable.comp (Computable.fst (α := ℕ) (β := ℕ))
  have hab := family_answersB_computable.comp (Computable.fst (α := ℕ) (β := ℕ))
  have hB := csucc _ hqb
  have hC := csucc _ haa
  have hD := csucc _ hab
  have hCD := cmul _ _ hC hD
  have hxy := cdiv (fun z : ℕ × ℕ => z.2) _ Computable.snd hCD
  have hab' := cmod (fun z : ℕ × ℕ => z.2) _ Computable.snd hCD
  have hx := cdiv _ _ hxy hB
  have hy := cmod _ _ hxy hB
  have ha := cdiv _ _ hab' hD
  have hb := cmod _ _ hab' hD
  have hc := cacceptsRowNat _ _ _ _ _ hP hx hy ha hb
  exact hc.of_eq (fun z => by unfold acceptanceFamily; rfl)

theorem entries_table_eq {α : Type} {A B : ℕ} (entry : ℕ → ℕ → α) (e : ℕ)
    (hB : 0<B) (f : Fin A → Fin B → α)
    (h : ∀ k : Fin (A*B), entry e k.val=f (GameTable.first hB k) (GameTable.second hB k)) :
    entries entry e (A*B)=GameTable.table hB f := by
  rw [entries_ofFn]
  unfold GameTable.table
  exact congrArg List.ofFn (funext h)

theorem entries_table4_eq {α : Type} {A B C D : ℕ} (entry : ℕ → ℕ → α) (e : ℕ)
    (hB : 0<B) (hC : 0<C) (hD : 0<D) (f : Fin A → Fin B → Fin C → Fin D → α)
    (h : ∀ k : Fin ((A*B)*(C*D)), entry e k.val=
      f (GameTable.first hB (GameTable.first (Nat.mul_pos hC hD) k))
        (GameTable.second hB (GameTable.first (Nat.mul_pos hC hD) k))
        (GameTable.first hD (GameTable.second (Nat.mul_pos hC hD) k))
        (GameTable.second hD (GameTable.second (Nat.mul_pos hC hD) k))) :
    entries entry e (A*B*C*D)=GameTable.table4 hB hC hD f := by
  calc
    _ = entries entry e ((A*B)*(C*D)) := congrArg (entries entry e) (Nat.mul_assoc (A*B) C D)
    _ = _ := by
      rw [entries_ofFn]
      unfold GameTable.table4 GameTable.table
      exact congrArg List.ofFn (funext h)

set_option allowUnsafeReducibility true in
attribute [local reducible] scenarioFamily

theorem distributionFamily_eq (n k : ℕ)
    (x : QA (finalGame (decodedPresentation n)).scenario)
    (y : QB (finalGame (decodedPresentation n)).scenario) :
    distributionFamily n k=(finalGame (decodedPresentation n)).distribution x y := by
  unfold distributionFamily scenarioFamily finalGame RowGame.game
  rfl

theorem acceptanceFamily_eq (n : ℕ)
    (k : Fin (((scenarioFamily n).questionsA+1)*((scenarioFamily n).questionsB+1)*
      (((scenarioFamily n).answersA+1)*((scenarioFamily n).answersB+1)))) :
    acceptanceFamily n k.val=(finalGame (decodedPresentation n)).accepts
      (GameTable.first (by omega) (GameTable.first (by positivity) k))
      (GameTable.second (by omega) (GameTable.first (by positivity) k))
      (GameTable.first (by omega) (GameTable.second (by positivity) k))
      (GameTable.second (by omega) (GameTable.second (by positivity) k)) := by
  unfold acceptanceFamily
  exact final_acceptsNat_eq (decodedPresentation n)
    (GameTable.first (by omega) (GameTable.first (by positivity) k))
    (GameTable.second (by omega) (GameTable.first (by positivity) k))
    (GameTable.first (by omega) (GameTable.second (by positivity) k))
    (GameTable.second (by omega) (GameTable.second (by positivity) k))

theorem distribution_table_eq (n : ℕ) :
    entries distributionFamily n (questionCount (scenarioFamily n))=
      GameTable.table (by omega) (finalGame (decodedPresentation n)).distribution := by
  apply entries_table_eq
  intro k
  exact distributionFamily_eq n k.val _ _

theorem acceptance_table_eq (n : ℕ) :
    entries acceptanceFamily n (outcomeCount (scenarioFamily n))=
      GameTable.table4 (by omega) (by omega) (by omega) (finalGame (decodedPresentation n)).accepts := by
  apply entries_table4_eq
  exact acceptanceFamily_eq n

theorem rawFamily_eq (n : ℕ) :
    rawFamily scenarioFamily distributionFamily acceptanceFamily n=
      GameTable.raw (finalGame (decodedPresentation n)) := by
  unfold rawFamily GameTable.raw
  exact congrArg₂ (fun d a => (scenarioFamily n,d,a)) (distribution_table_eq n) (acceptance_table_eq n)

theorem rawFamily_eq_of_decode (n : ℕ) (P : Presentation)
    (h : Encodable.decode (α := Presentation) n=some P) :
    rawFamily scenarioFamily distributionFamily acceptanceFamily n=GameTable.raw (finalGame P) := by
  have hd : decodedPresentation n=P := by unfold decodedPresentation; rw [h]; rfl
  exact (rawFamily_eq n).trans (congrArg (fun Q => GameTable.raw (finalGame Q)) hd)

#print axioms distributionFamily_computable
#print axioms acceptanceFamily_computable
#print axioms entries_table4_eq
#print axioms rawFamily_eq_of_decode
end Sigma2.CompilerEffectiveCoding