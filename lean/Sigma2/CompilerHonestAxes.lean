import Sigma2.CompilerHonestAxisCertificate

/-! The actual frozen positive-axis parameters are precisely both FMS coarse
effects, lifted to the common infinite-dimensional register. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestAxes
open Compiler CompilerScaffold CompilerHonestScalar CompilerHonestFamilies
  CompilerFiniteRegister CompilerHonestFMSLift FiniteAncilla

def perm (e : Equiv.Perm (Fin 17)) : Matrix (Fin 17) (Fin 17) ℂ :=
  fun i j => if j=e i then 1 else 0

def magicMatrix (g : Fin 4) : Matrix (Fin 17) (Fin 17) ℂ :=
  Matrix.diagonal (fun i => if magicActive g i then 1 else 0)

theorem scalar_smul (d : ℕ) [NeZero d] (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    scalarOp d (c • A)=c • scalarOp d A := by
  unfold scalarOp
  rw [← matrixOp_smul]
  congr 1
  apply Matrix.ext
  intro i j
  simp [blocks,smul_smul]

theorem zero_smul_op (A : Op) : (0:ℂ) • A=0 := by
  ext v i
  simp

theorem scalar_perm (e : Equiv.Perm (Fin 17)) : scalarOp 17 (perm e)=permutation 17 e := by
  unfold scalarOp permutation
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : j=e i <;> simp [blocks,perm,RowCompleteness.permutationMatrix,hij,zero_smul_op]

theorem scalar_magic (g : Fin 4) : scalarOp 17 (magicMatrix g)=mask 17 (magicActive g) := by
  unfold scalarOp magicMatrix mask diagonal
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    by_cases hi : magicActive g i <;> simp [blocks,hi,zero_smul_op]
  · simp [blocks,Matrix.diagonal_apply,hij,zero_smul_op]

theorem local_axis (g : Fin 4) (k : Fin 2) :
    embed (position g) (CompilerHonestFMS.parameter k)=
      magicMatrix g*((1/2:ℂ) • (1+perm (axisPerm g k))) := by
  have hp : CompilerHonestAxisCertificate.ratMatrix
      (CompilerHonestAxisCertificate.permutationQ g k)=perm (axisPerm g k) := by
    apply Matrix.ext
    intro i j
    by_cases hij : j=axisPerm g k i <;>
      simp [CompilerHonestAxisCertificate.ratMatrix,
        CompilerHonestAxisCertificate.permutationQ,perm,hij]
  have hh := congrArg CompilerHonestAxisCertificate.ratMatrix
    (CompilerHonestAxisCertificate.certificate g k)
  simp only [CompilerHonestAxisCertificate.ratMatrix_mul,
    CompilerHonestAxisCertificate.ratMatrix_transpose,
    CompilerHonestAxisCertificate.ratMatrix_smul,
    CompilerHonestAxisCertificate.ratMatrix_add,
    CompilerHonestAxisCertificate.ratMatrix_one,
    CompilerHonestAxisCertificate.cast_parameter,
    CompilerHonestAxisCertificate.cast_inclusion,
    hp,
    CompilerHonestAxisCertificate.cast_magic] at hh
  norm_num only [Rat.cast_div,Rat.cast_natCast] at hh
  simpa only [embed,magicMatrix,one_div] using hh

theorem actual_axis (g : Fin 4) (k : Fin 2) :
    scalarOp 17 (embed (position g) (CompilerHonestFMS.parameter k))=
      CompilerHonestDictionary.parameter (17+2*g.val+k.val) := by
  rw [local_axis,scalar_mul,scalar_smul,scalar_add,scalar_one,scalar_perm,scalar_magic]
  have hg := g.isLt
  have hk := k.isLt
  simp only [CompilerHonestDictionary.parameter]
  rw [dif_neg (by omega),dif_pos (by omega)]
  have he : (⟨(17+2*g.val+k.val-17)/2,by omega⟩ : Fin 4)=g := by
    apply Fin.ext
    change (17+2*g.val+k.val-17)/2=g.val
    omega
  have hf : (⟨(17+2*g.val+k.val-17)%2,by omega⟩ : Fin 2)=k := by
    apply Fin.ext
    change (17+2*g.val+k.val-17)%2=k.val
    omega
  rw [he,hf]
  rfl

theorem alice_coarse (g : Fin 4) (k : Fin 2) :
    (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false
      then (CompilerHonestFamilies.alice g (if k=0 then 1 else 0)).effect a else 0)=
        embed (position g) (CompilerHonestFMS.parameter k) := by
  rw [← CompilerHonestFMS.alice_axis_binding,embed_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false
  · have hn : a≠5 := by intro h; subst a; norm_num at he
    simp only [he,true_and,ite_true,CompilerHonestFMSWeights.alice_effect,hn,ite_false,add_zero]
  · simp only [he,ite_false,embed_zero]

theorem bob_coarse (g : Fin 4) (k : Fin 2) :
    (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧
      cellSign false (a.val-1) (if k=0 then 1 else 0)=false
      then (CompilerHonestFamilies.bob g 1).effect a else 0)=
        embed (position g) (CompilerHonestFMS.parameter k) := by
  rw [← CompilerHonestFMS.bob_axis_binding,embed_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases he : 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) (if k=0 then 1 else 0)=false
  · have hn : a≠5 := by intro h; subst a; norm_num at he
    simp only [he,true_and,ite_true,CompilerHonestFMSWeights.bob_effect,hn,ite_false,add_zero]
  · simp only [he,ite_false,embed_zero]

/-- The actual Alice coarse operator, after both common ancillary lifts. -/
theorem alice_axis_binding (g : Fin 4) (k : Fin 2) :
    (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false
      then (CompilerHonestFMSLift.alice g (if k=0 then 1 else 0)).effect a else 0)=
        amplify 3 (CompilerHonestDictionary.parameter (17+2*g.val+k.val)) := by
  rw [← actual_axis]
  calc
    _=amplify 3 (scalarOp 17 (∑ a : Fin 6,
        if 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false
        then (CompilerHonestFamilies.alice g (if k=0 then 1 else 0)).effect a else 0)) := by
      rw [scalar_sum,amplify_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp only [CompilerHonestFMSLift.alice,amplifyPartition,
        scalarPartition,scalar_zero,amplify_zero_eq]
    _=_ := by rw [alice_coarse]

/-- The actual Bob coarse operator has the same numbered parameter value. -/
theorem bob_axis_binding (g : Fin 4) (k : Fin 2) :
    (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧
      cellSign false (a.val-1) (if k=0 then 1 else 0)=false
      then (CompilerHonestFMSLift.bob g 1).effect a else 0)=
        amplify 3 (CompilerHonestDictionary.parameter (17+2*g.val+k.val)) := by
  rw [← actual_axis]
  calc
    _=amplify 3 (scalarOp 17 (∑ a : Fin 6,
        if 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) (if k=0 then 1 else 0)=false
        then (CompilerHonestFamilies.bob g 1).effect a else 0)) := by
      rw [scalar_sum,amplify_sum]
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> simp only [CompilerHonestFMSLift.bob,amplifyPartition,
        scalarPartition,scalar_zero,amplify_zero_eq]
    _=_ := by rw [bob_coarse]

#print axioms actual_axis
#print axioms alice_coarse
#print axioms bob_coarse
#print axioms alice_axis_binding
#print axioms bob_axis_binding
end Sigma2.CompilerHonestAxes
