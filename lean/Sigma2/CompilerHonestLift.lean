import Sigma2.CompilerHonestPrerequisites

/-! A common rectangular lift into the actual seventeen-corner register.
In particular, all four lifted creations are centralizer contractions for the
same weighted density and receive exact two-unitary encodings. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestLift
open Compiler CompilerApproxBlocks CompilerHonestDensity FiniteAncilla FiniteSum
variable (d : ℕ) [NeZero d]

def lift (a b : Fin d) (A : Op) : Op := matrixOp d (singleBlocks d a b A)

@[simp] theorem lift_zero (a b : Fin d) : lift d a b 0=0 := by
  have h : singleBlocks d a b 0=0 := by ext i j; simp [singleBlocks]
  rw [lift,h,matrixOp_zero]

@[simp] theorem lift_star (a b : Fin d) (A : Op) :
    star (lift d a b A)=lift d b a (star A) := by
  rw [lift,← matrixOp_star,single_star]
  rfl

@[simp] theorem lift_mul (a b c z : Fin d) (A B : Op) :
    lift d a b A*lift d c z B=if b=c then lift d a z (A*B) else 0 := by
  rw [lift,lift,← matrixOp_mul,single_mul]
  split_ifs <;> simp [lift]

@[simp] theorem lift_fiber (a b : Fin d) (A : Op) (v : H) (i : Fin d) :
    fiber (coordinates d) (lift d a b A v) i=
      if i=a then A (fiber (coordinates d) v b) else 0 := by
  rw [lift,fiber_matrixOp,Finset.sum_eq_single b]
  · by_cases hi : i=a <;> simp [singleBlocks,hi]
  · intro j hj hjb
    simp [singleBlocks,hjb]
  · simp

theorem lift_apply (a b : Fin d) (A : Op) (v : H) :
    lift d a b A v=FiniteSum.insert (coordinates d) a (A (fiber (coordinates d) v b)) := by
  apply ext_fiber (coordinates d)
  intro i
  rw [lift_fiber,fiber_insert]

theorem lift_contraction (a b : Fin d) (A : Op) (hA : Contraction A) :
    Contraction (lift d a b A) := by
  change ‖lift d a b A‖≤1
  change ‖A‖≤1 at hA
  apply (lift d a b A).opNorm_le_bound (by norm_num)
  intro v
  rw [lift_apply,LinearIsometry.norm_map,one_mul]
  calc
    ‖A (fiber (coordinates d) v b)‖ ≤ ‖A‖*‖fiber (coordinates d) v b‖ := A.le_opNorm _
    _ ≤ 1*‖fiber (coordinates d) v b‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ ≤ ‖v‖ := by rw [one_mul]; exact fiber_bound (coordinates d) b v

theorem single_diagonal (w : Fin d → ℝ) (A B : Op) (a b : Fin d) :
    singleBlocks d a b A*diagonalBlocks d w B=
      singleBlocks d a b ((w b:ℂ) • (A*B)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply,Finset.sum_eq_single b]
  · by_cases hi : i=a <;> by_cases hj : j=b <;>
      simp_all [diagonalBlocks,singleBlocks,mul_smul_comm]
    all_goals aesop
  · intro k hk hkb
    have hz : singleBlocks d a b A i k=0 := by simp [singleBlocks,hkb]
    rw [hz,zero_mul]
  · simp

theorem lift_centralizer (w : Fin d → ℝ) (D A : Op) (a b : Fin d)
    (h : (w a:ℂ) • (D*A)=(w b:ℂ) • (A*D)) :
    Centralizes (weightedOp d w D) (lift d a b A) := by
  change matrixOp d (diagonalBlocks d w D)*matrixOp d (singleBlocks d a b A)=
    matrixOp d (singleBlocks d a b A)*matrixOp d (diagonalBlocks d w D)
  rw [← matrixOp_mul,← matrixOp_mul,diagonal_single,single_diagonal,h]

theorem lift_supported_right (a b : Fin d) (A e : Op) (hAe : A*e=A) :
    lift d a b A*amplify d e=lift d a b A := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro i
  rw [mul_apply_eq_comp,lift_fiber,lift_fiber,fiber_amplify]
  by_cases hi : i=a
  · rw [if_pos hi,if_pos hi]
    exact congrArg (fun B : Op => B (fiber (coordinates d) v b)) hAe
  · rw [if_neg hi,if_neg hi]

theorem creation_lift_centralizer {P : Presentation} (R : StructuralRealization P) (a : Fin 4) :
    Centralizes (scaffoldDensity R.density).op (lift 17 13 0 (R.creation a)) := by
  apply lift_centralizer
  norm_num [CompilerScaffold.cornerWeight]
  rw [R.modular]
  module

/-- Exact simultaneous encoding for all four creations. There is one density
and one coordinate register, with no separate bridge gauges. -/
theorem creation_encodings {P : Presentation} (R : StructuralRealization P) :
    ∃ U V : Fin 4 → Op,
      (∀ a,Unitary (U a) ∧ Unitary (V a)) ∧
      (∀ a,Centralizes (scaffoldDensity R.density).op (U a) ∧
        Centralizes (scaffoldDensity R.density).op (V a)) ∧
      (∀ a,lift 17 13 0 (R.creation a)=(1/2:ℂ) • (U a+V a)) := by
  have he : Preliminaries.SupportOf R.density R.support :=
    ⟨R.support_projection,R.density_supported,R.faithful_on⟩
  have hs := scaffold_support R.density R.support he
  have h (a : Fin 4) := CompilerHonestEncoding.supported_mean
    (scaffoldDensity R.density) (amplify 17 R.support) (lift 17 13 0 (R.creation a)) hs
    (lift_contraction 17 _ _ _ (R.creation_contractive a))
    (creation_lift_centralizer R a)
    (lift_supported_right 17 _ _ _ _ (R.creation_supported a).2)
  choose U V hU hV hcU hcV hm hker using h
  exact ⟨U,V,fun a => ⟨hU a,hV a⟩,fun a => ⟨hcU a,hcV a⟩,hm⟩

#print axioms creation_lift_centralizer
#print axioms creation_encodings
end Sigma2.CompilerHonestLift
