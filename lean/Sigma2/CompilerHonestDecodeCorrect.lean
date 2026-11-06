import Sigma2.CompilerHonestRefinementsCorrect

/-! Bounds and exact padded effects for the frozen pregame decoder. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
noncomputable section
namespace Sigma2.CompilerHonestDecodeCorrect
open Compiler CompilerScaffold CompilerHonestRefinementsCorrect CompilerHonestPregameBase
  CompilerProjectionDictionary CompilerHonestState CoefficientOperator RowCompleteness
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

def WellFormed (P : Presentation) : Question → Prop
  | .fms g x => g<4 ∧ x<5
  | .refinement g k => g<4 ∧ k<6+encodingCount P
  | _ => True

theorem question_wellFormed (P : Presentation) (n : ℕ) : WellFormed P (question P n) := by
  dsimp only [question]
  split_ifs with h0 h1 h2
  · trivial
  · change (n-(names P).length)/5<4 ∧ (n-(names P).length)%5<5
    omega
  · change (n-(names P).length-20)/(6+encodingCount P)<4 ∧
      (n-(names P).length-20)%(6+encodingCount P)<6+encodingCount P
    constructor
    · apply (Nat.div_lt_iff_lt_mul (by omega : 0<6+encodingCount P)).mpr
      unfold refinementCount at h2
      omega
    · exact Nat.mod_lt _ (by omega)
  · trivial

def localPartition {P : Presentation} (R : StructuralRealization P) (bob : Bool) (q : Question) :
    Partition Op (Fin 12) :=
  CompilerHonestPregameBase.localPartition R bob (refinements R bob) q

theorem pad_value (Q : Partition Op (Fin 6)) (a : Fin 12) (ha : a.val<6) :
    (pad Q).effect a=Q.effect ⟨a.val,ha⟩ :=
  pad_effect Q ⟨a.val,ha⟩

theorem binary_value (E : Op) (hE : Projection E) (a : Fin 12) (ha : a.val<2) :
    (binary E hE).effect a=(Partition.binary E hE.1 hE.2).effect (decide (a.val=1)) := by
  have he : CompilerHonestPregameBase.bit (decide (a.val=1))=a := by
    apply Fin.ext
    simp only [CompilerHonestPregameBase.bit,Bool.decide_iff]
    split_ifs <;> omega
  conv_lhs => rw [← he]
  exact Partition.coarse_injective _ CompilerHonestPregameBase.bit bit_injective _

theorem fms_value {P : Presentation} (R : StructuralRealization P) (bob : Bool)
    (g : Fin 4) (x : Fin 5) (a : Fin 12) (ha : a.val<6) :
    (localPartition R bob (.fms g.val x.val)).effect a=
      (CompilerHonestRefinementCommute.fms bob g x).effect ⟨a.val,ha⟩ := by
  simp only [localPartition,CompilerHonestPregameBase.localPartition]
  rw [dif_pos g.isLt,dif_pos x.isLt]
  exact pad_value _ a ha

theorem refinement_value {P : Presentation} (R : StructuralRealization P) (bob : Bool)
    (g : Fin 4) (k : Fin (6+encodingCount P)) :
    localPartition R bob (.refinement g.val k.val)=
      if bob then CompilerHonestRefinementsCorrect.bob R g k else CompilerHonestRefinementsCorrect.alice R g k := by
  change refinements R bob g.val k.val=_
  rw [refinements,dif_pos g.isLt,dif_pos k.isLt]

/-- Every padded or invalid answer has exactly zero local effect. -/
theorem invalid_zero {P : Presentation} (R : StructuralRealization P) (bob : Bool)
    (q : Question) (a : Fin 12) (ha : valid q a.val=false) :
    (localPartition R bob q).effect a=0 := by
  cases q with
  | binary n =>
      have hv : 2≤a.val := by simpa only [valid,decide_eq_false_iff_not,not_lt] using ha
      simp only [localPartition,CompilerHonestPregameBase.localPartition]
      split_ifs
      all_goals
        apply Partition.coarse_outside
        intro b he
        have hh := congrArg Fin.val he
        cases b <;> simp [CompilerHonestPregameBase.bit] at hh <;> omega
  | fms g x =>
      have hv : 6≤a.val := by simpa only [valid,decide_eq_false_iff_not,not_lt] using ha
      simp only [localPartition,CompilerHonestPregameBase.localPartition]
      split_ifs
      all_goals first
        | apply Partition.coarse_outside
          intro b he
          have hh : b.val=a.val := congrArg Fin.val he
          have := b.isLt
          omega
        | change (if a=0 then (1:Op) else 0)=0
          rw [if_neg (by intro h; have he : a.val=0 := congrArg Fin.val h; omega)]
  | refinement g k =>
      have := a.isLt
      simp only [valid,decide_eq_false_iff_not] at ha
      exact (ha this).elim
  | padding =>
      have hv : a≠0 := by intro h; subst a; simp [valid] at ha
      change (if a=0 then (1:Op) else 0)=0
      rw [if_neg hv]

#print axioms question_wellFormed
#print axioms invalid_zero
end Sigma2.CompilerHonestDecodeCorrect
