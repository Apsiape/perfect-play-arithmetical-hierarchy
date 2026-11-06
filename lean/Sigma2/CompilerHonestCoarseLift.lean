import Sigma2.CompilerHonestCoarse
import Sigma2.CompilerHonestRefinementCommute

/-! Activity, flag and chosen-magic coarse bindings for the genuine operators
 on the common qutrit/scaffold Hilbert space. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestCoarseLift
open Compiler CompilerScaffold CompilerHonestCoarse CompilerHonestFamilies
  CompilerHonestScalar CompilerHonestFMSWeights CompilerProjectionDictionary
  CompilerFiniteRegister CompilerHonestDictionary CompilerHonestFMSLift
  CompilerHonestRefinementCommute FiniteAncilla CoefficientOperator RowCompleteness

theorem scalar_corner (i : Fin 17) :
    scalarOp 17 (Matrix.diagonal (fun j => if j=i then (1:ℂ) else 0))=CompilerFiniteRegister.corner 17 i := by
  unfold scalarOp CompilerFiniteRegister.corner diagonal
  congr 1
  apply Matrix.ext
  intro j k
  by_cases he : j=k <;> by_cases hi : j=i <;>
    simp [blocks,Matrix.diagonal_apply,he,hi,CompilerHonestAxes.zero_smul_op]

theorem scalar_active (g : Fin 4) : scalarOp 17 (active g)=mask 17 (bridgeActive g.val) := by
  rw [active_diagonal]
  unfold scalarOp mask diagonal
  congr 1
  apply Matrix.ext
  intro i j
  by_cases he : i=j <;> by_cases hi : bridgeActive g.val i <;>
    simp [blocks,Matrix.diagonal_apply,he,hi,CompilerHonestAxes.zero_smul_op]

theorem scalar_embedded_corner (g : Fin 4) (a : Fin 5) :
    scalarOp 17 (embed (position g) (localCorner a))=CompilerFiniteRegister.corner 17 (position g a) := by
  rw [embedded_corner,scalar_corner]

theorem parameter_transpose (i : Fin 17) :
    transpose (CompilerHonestDictionary.parameter i.val)=CompilerHonestDictionary.parameter i.val := by
  simp only [CompilerHonestDictionary.parameter,dif_pos i.isLt]
  rw [← scalar_corner,transpose_scalar]
  congr 1
  ext j k
  by_cases h : j=k <;> simp [Matrix.transpose_apply,Matrix.diagonal_apply,h,Ne.symm]

/-- Both local FMS orientations have the same activity coarse operator. -/
theorem activity_binding {P : Presentation} (R : StructuralRealization P)
    (bob : Bool) (g : Fin 4) (x : Fin 5) :
    (∑ a : Fin 6,if a.val<5 then (fms bob g x).effect a else 0)=projection R (.active g.val) := by
  calc
    _=amplify 3 (scalarOp 17 (∑ a : Fin 6,if a.val<5 then
      (if bob then CompilerHonestFamilies.bob g x else CompilerHonestFamilies.alice g x).effect a else 0)) := by
      rw [scalar_sum,amplify_sum]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases h : a.val<5 <;> simp only [h,ite_true,ite_false,fms_effect,core,scalar_zero,amplify_zero_eq]
    _=amplify 3 (scalarOp 17 (active g)) := by
      congr 2
      cases bob
      · exact activity_sum g _ (by simp [CompilerHonestFMS.alicePartition,
          CompilerHonestFMS.alice,CompilerHonestFMS.rankOne,CompilerHonestFMS.aliceVector_inactive])
      · exact activity_sum g _ (by simp [CompilerHonestFMS.bobPartition,
          CompilerHonestFMS.bob,CompilerHonestFMS.rankOne,CompilerHonestFMS.bobVector_inactive])
    _=_ := by rw [scalar_active]; rfl

theorem flag_binding {P : Presentation} (R : StructuralRealization P)
    (bob : Bool) (g : Fin 4) (x : Fin 3) :
    (fms bob g ⟨x.val,by have := x.isLt; omega⟩).effect 0=
      projection R (.parameter (cornerIndex g.val)) := by
  rw [fms_effect]
  unfold core
  have he : (if bob then CompilerHonestFamilies.bob g ⟨x.val,by have := x.isLt; omega⟩
      else CompilerHonestFamilies.alice g ⟨x.val,by have := x.isLt; omega⟩).effect 0=
      embed (position g) (localCorner 0) := by
    cases bob <;> simp [CompilerHonestFMSWeights.alice_effect,
      CompilerHonestFMSWeights.bob_effect,alice_flag,bob_flag]
  rw [he,scalar_embedded_corner]
  have hg := g.isLt
  have hn : cornerIndex g.val<17 := by unfold cornerIndex; split_ifs <;> omega
  change amplify 3 _=amplify 3 (CompilerHonestDictionary.parameter _)
  rw [CompilerHonestDictionary.parameter,dif_pos hn]
  congr 2

theorem alice_magic_binding {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin 4) :
    (CompilerHonestFMSLift.alice g (if k=0 then 4 else 3)).effect
      ⟨if k=0 then 2 else k.val+1,by have := k.isLt; split_ifs <;> omega⟩=
      projection R (.parameter (1+4*g.val+k.val)) := by
  change amplify 3 (scalarOp 17 ((CompilerHonestFamilies.alice g _).effect _))=_
  rw [CompilerHonestFMSWeights.alice_effect,alice_magic]
  have ha : (⟨if k=0 then 2 else k.val+1,by have := k.isLt; split_ifs <;> omega⟩ : Fin 6)≠5 := by
    fin_cases k <;> decide
  rw [if_neg ha,add_zero,scalar_embedded_corner]
  have hn : 1+4*g.val+k.val<17 := by have := g.isLt; have := k.isLt; omega
  change amplify 3 _=amplify 3 (CompilerHonestDictionary.parameter _)
  rw [CompilerHonestDictionary.parameter,dif_pos hn]
  congr 2
  apply Fin.ext
  have hk : (⟨k.val+1,by have := k.isLt; omega⟩ : Fin 5)≠0 := by
    intro h; have := congrArg Fin.val h; simp at this
  simp only [position,dif_neg hk]
  omega

theorem bob_magic_binding {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (k : Fin 4) :
    (CompilerHonestFMSLift.bob g 0).effect ⟨k.val+1,by have := k.isLt; omega⟩=
      projection R (.parameter (1+4*g.val+k.val)) := by
  change amplify 3 (scalarOp 17 ((CompilerHonestFamilies.bob g _).effect _))=_
  rw [CompilerHonestFMSWeights.bob_effect,bob_magic]
  have ha : (⟨k.val+1,by have := k.isLt; omega⟩ : Fin 6)≠5 := by
    intro h
    have he : k.val+1=5 := congrArg Fin.val h
    have := k.isLt
    omega
  rw [if_neg ha,add_zero,scalar_embedded_corner]
  have hn : 1+4*g.val+k.val<17 := by have := g.isLt; have := k.isLt; omega
  change amplify 3 _=amplify 3 (CompilerHonestDictionary.parameter _)
  rw [CompilerHonestDictionary.parameter,dif_pos hn]
  congr 2
  apply Fin.ext
  have hk : (⟨k.val+1,by have := k.isLt; omega⟩ : Fin 5)≠0 := by
    intro h; have := congrArg Fin.val h; simp at this
  simp only [position,dif_neg hk]
  omega

#print axioms activity_binding
#print axioms flag_binding
#print axioms alice_magic_binding
#print axioms bob_magic_binding
end Sigma2.CompilerHonestCoarseLift
