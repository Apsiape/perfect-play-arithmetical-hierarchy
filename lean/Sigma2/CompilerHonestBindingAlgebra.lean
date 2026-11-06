import Sigma2.CompilerHonestRefinements

/-! Coarse binary bindings are rejection annihilators for arbitrary projection
 partitions, with either question orientation. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestBindingAlgebra
open Compiler RowCompleteness TensorLifts
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem coarse_binary_product (Q : Partition Op ι) (f : ι → Bool) (E : Op)
    (hE : Projection E) (he : (Q.coarse f).effect true=E) (a : ι) (b : Bool)
    (hr : f a≠b) : Q.effect a*(Partition.binary E hE.1 hE.2).effect b=0 := by
  cases b
  · have hf : f a=true := by cases h : f a <;> simp_all
    change Q.effect a*(1-E)=0
    rw [mul_sub,mul_one,← he,Partition.coarse_action,if_pos hf,sub_self]
  · change Q.effect a*E=0
    rw [← he,Partition.coarse_action,if_neg hr]

theorem alice_zero (Q : Partition Op ι) (f : ι → Bool) (E F : Op)
    (hE : Projection E) (hF : Projection F) (he : (Q.coarse f).effect true=E)
    (v : AB) (hm : left E v=right F v) (a : ι) (b : Bool) (hr : f a≠b) :
    (left (Q.effect a)*right ((Partition.binary F hF.1 hF.2).effect b)) v=0 := by
  change left _ (right _ v)=0
  rw [← binary_mirror E F hE hF v hm b,← mul_apply_eq_comp,← left_mul,
    coarse_binary_product Q f E hE he a b hr,CoarseCells.left_zero,zero_apply]

theorem bob_zero (Q : Partition Op ι) (f : ι → Bool) (E F : Op)
    (hE : Projection E) (hF : Projection F) (he : (Q.coarse f).effect true=F)
    (v : AB) (hm : left E v=right F v) (a : Bool) (b : ι) (hr : f b≠a) :
    (left ((Partition.binary E hE.1 hE.2).effect a)*right (Q.effect b)) v=0 := by
  rw [TensorLifts.commute]
  change right _ (left _ v)=0
  rw [binary_mirror E F hE hF v hm a,← mul_apply_eq_comp,← right_mul,
    coarse_binary_product Q f F hF he b a hr,CoarseCells.right_zero,zero_apply]

#print axioms alice_zero
#print axioms bob_zero
end Sigma2.CompilerHonestBindingAlgebra
