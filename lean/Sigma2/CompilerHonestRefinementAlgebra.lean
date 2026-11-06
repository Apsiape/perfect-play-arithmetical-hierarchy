import Sigma2.CompilerHonestMeasurements

/-! Binary refinements with the exact twelve-answer encoding of the frozen
 verifier. These constructions use one label at a time. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestRefinementAlgebra
open Compiler RowCompleteness CompilerHonestState CoefficientOperator
abbrev Answers := Fin 12

def pack (ab : Fin 6 × Bool) : Answers :=
  ⟨2*ab.1.val+(if ab.2 then 1 else 0),by have := ab.1.isLt; split_ifs <;> omega⟩
def unpack (a : Answers) : Fin 6 × Bool :=
  (⟨a.val/2,by have := a.isLt; omega⟩,decide (a.val%2=1))

theorem pack_unpack (a : Answers) : pack (unpack a)=a := by
  apply Fin.ext
  simp only [pack,unpack,Bool.decide_iff]
  split_ifs <;> omega

theorem unpack_pack (ab : Fin 6 × Bool) : unpack (pack ab)=ab := by
  rcases ab with ⟨a,b⟩
  cases b <;> apply Prod.ext
  all_goals simp [pack,unpack,Fin.ext_iff] <;> omega

theorem pack_injective : Function.Injective pack := by
  intro a b h
  simpa only [unpack_pack] using congrArg unpack h

def refine (Q : Partition Op (Fin 6)) (E : Op) (hE : Projection E)
    (hc : ∀ a,Commute (Q.effect a) E) : Partition Op Answers :=
  (Q.joint (Partition.binary E hE.1 hE.2) (by
    intro a b
    cases b
    · exact ((Commute.one_right (Q.effect a)).sub_right (hc a)).eq
    · exact (hc a).eq)).coarse pack

theorem refine_effect (Q : Partition Op (Fin 6)) (E : Op) (hE : Projection E)
    (hc : ∀ a,Commute (Q.effect a) E) (a : Answers) :
    (refine Q E hE hc).effect a=
      Q.effect (unpack a).1*(if (unpack a).2 then E else 1-E) := by
  conv_lhs => rw [← pack_unpack a]
  exact Partition.coarse_injective _ pack pack_injective (unpack a)

/-- Every retained Alice FMS rejection survives its separate refinement. -/
theorem refine_left_zero (Q : Partition Op (Fin 6)) (E : Op) (hE : Projection E)
    (hc : ∀ a,Commute (Q.effect a) E) (T B : Op) (a : Answers)
    (hz : Q.effect (unpack a).1*T*B=0) :
    (refine Q E hE hc).effect a*T*B=0 := by
  rw [refine_effect]
  have he : Commute (Q.effect (unpack a).1) (if (unpack a).2 then E else 1-E) := by
    split_ifs
    · exact hc _
    · exact (Commute.one_right (Q.effect (unpack a).1)).sub_right (hc _)
  rw [he.eq,mul_assoc, mul_assoc,← mul_assoc (Q.effect _),hz,mul_zero]

/-- The same statement in the reverse orientation, retaining the actual
 transpose convention of Bob's coefficient operator. -/
theorem refine_right_zero (Q : Partition Op (Fin 6)) (E : Op) (hE : Projection E)
    (hc : ∀ a,Commute (Q.effect a) E) (A T : Op) (a : Answers)
    (hz : A*T*transpose (Q.effect (unpack a).1)=0) :
    A*T*transpose ((refine Q E hE hc).effect a)=0 := by
  rw [refine_effect]
  have he : Commute (Q.effect (unpack a).1) (if (unpack a).2 then E else 1-E) := by
    split_ifs
    · exact hc _
    · exact (Commute.one_right (Q.effect (unpack a).1)).sub_right (hc _)
  rw [he.eq,transpose_mul,← mul_assoc,hz,zero_mul]

/-- A disagreeing binary label is an actual zero operator product. -/
theorem refine_label_zero (Q : Partition Op (Fin 6)) (E : Op) (hE : Projection E)
    (hc : ∀ a,Commute (Q.effect a) E) (a : Answers) (b : Bool)
    (hb : (unpack a).2≠b) :
    (refine Q E hE hc).effect a*(Partition.binary E hE.1 hE.2).effect b=0 := by
  rw [refine_effect,mul_assoc]
  change Q.effect (unpack a).1*((Partition.binary E hE.1 hE.2).effect (unpack a).2*
    (Partition.binary E hE.1 hE.2).effect b)=0
  rw [Partition.orthogonal _ _ _ hb,mul_zero]

#print axioms refine_left_zero
#print axioms refine_right_zero
#print axioms refine_label_zero
end Sigma2.CompilerHonestRefinementAlgebra
