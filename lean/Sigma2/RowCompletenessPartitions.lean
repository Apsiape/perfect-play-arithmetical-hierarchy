import Sigma2.RowCompletenessColumns

/-! Finite projective partitions and their simultaneous joint/coarse realization. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness

structure Partition (A : Type) [Ring A] [StarRing A] (ι : Type) [Fintype ι] [DecidableEq ι] where
  effect : ι → A
  selfadjoint : ∀ i, star (effect i)=effect i
  product : ∀ i j, effect i*effect j=if i=j then effect i else 0
  total : ∑ i,effect i=1

namespace Partition
variable {A : Type} [Ring A] [StarRing A]
variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

@[simp] theorem square (P : Partition A ι) (i : ι) : P.effect i*P.effect i=P.effect i := by
  rw [P.product,if_pos rfl]

@[simp] theorem orthogonal (P : Partition A ι) (i j : ι) (h : i≠j) :
    P.effect i*P.effect j=0 := by rw [P.product,if_neg h]

/-- Coarsening preserves the complete finite partition, including empty fibers. -/
def coarse (P : Partition A ι) (f : ι → κ) : Partition A κ where
  effect k := ∑ i,if f i=k then P.effect i else 0
  selfadjoint k := by simp only [star_sum]; congr 1; funext i; split_ifs <;> simp [P.selfadjoint]
  product k l := by
    classical
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    have he (i : ι) :
        (∑ j,(if f i=k then P.effect i else 0)*(if f j=l then P.effect j else 0))=
          if k=l then (if f i=k then P.effect i else 0) else 0 := by
      by_cases hi : f i=k
      · simp only [hi,ite_true,P.product,mul_ite,mul_zero]
        rw [Finset.sum_eq_single i]
        · by_cases hkl : k=l <;> simp [hi,hkl]
        · intro j hj hji; simp [Ne.symm hji]
        · simp
      · simp [hi]
    simp_rw [he]
    split_ifs <;> simp
  total := by
    classical
    rw [Finset.sum_comm]
    simpa using P.total

theorem coarse_single (P : Partition A ι) (f : ι → κ) (k : κ) (i₀ : ι)
    (hf : ∀ i,f i=k ↔ i=i₀) : (P.coarse f).effect k=P.effect i₀ := by
  change (∑ i,if f i=k then P.effect i else 0)=_
  simp only [hf,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

/-- Joint measurements for two commuting projection partitions. -/
def joint (P : Partition A ι) (Q : Partition A κ)
    (hc : ∀ i j,P.effect i*Q.effect j=Q.effect j*P.effect i) : Partition A (ι × κ) where
  effect ij := P.effect ij.1*Q.effect ij.2
  selfadjoint ij := by rw [star_mul,P.selfadjoint,Q.selfadjoint,← hc]
  product ij kl := by
    classical
    change (P.effect ij.1*Q.effect ij.2)*(P.effect kl.1*Q.effect kl.2)=_
    rw [mul_assoc,← mul_assoc (Q.effect ij.2),← hc,mul_assoc,← mul_assoc]
    rw [P.product,Q.product]
    by_cases hi : ij.1=kl.1 <;> by_cases hj : ij.2=kl.2 <;>
      simp [hi,hj,Prod.ext_iff]
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum,Q.total,mul_one,P.total]

/-- The standard binary measurement of a projection. -/
def binary (E : A) (hs : star E=E) (hp : E*E=E) : Partition A Bool where
  effect b := if b then E else 1-E
  selfadjoint b := by cases b <;> simp [hs]
  product b c := by
    cases b <;> cases c <;> simp [mul_sub,sub_mul,hp]
  total := by simp [Fintype.sum_bool]

/-- An injective outcome map pads a partition with zero effects. -/
theorem coarse_injective (P : Partition A ι) (f : ι → κ)
    (hf : Function.Injective f) (i : ι) : (P.coarse f).effect (f i)=P.effect i := by
  classical
  change (∑ j,if f j=f i then P.effect j else 0)=_
  simp only [hf.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem coarse_outside (P : Partition A ι) (f : ι → κ)
    (k : κ) (hk : ∀ i,f i≠k) : (P.coarse f).effect k=0 := by
  change (∑ i,if f i=k then P.effect i else 0)=0
  simp [hk]

/-- Coarse/fine compatibility, the algebraic source of rejection zeros. -/
theorem coarse_action (P : Partition A ι) (f : ι → κ)
    (i : ι) (k : κ) :
    P.effect i*(P.coarse f).effect k=if f i=k then P.effect i else 0 := by
  classical
  change P.effect i*(∑ j,if f j=k then P.effect j else 0)=_
  rw [Finset.mul_sum]
  simp only [mul_ite,mul_zero,P.product]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji; simp [Ne.symm hji]
  · simp

/-- A deterministic question has exactly one nonzero answer. -/
def deterministic (i₀ : ι) : Partition A ι where
  effect i := if i=i₀ then 1 else 0
  selfadjoint i := by split_ifs <;> simp
  product i j := by
    by_cases hi : i=i₀ <;> by_cases hj : j=i₀ <;> simp_all [eq_comm]
  total := by simp

/-- A common coarse label gives zero product for different labels. -/
theorem different_coarse (P : Partition A ι) (f : ι → κ) (i j : ι)
    (h : f i≠f j) : P.effect i*P.effect j=0 := by
  apply P.orthogonal
  intro he
  exact h (congrArg f he)

theorem joint_left (P : Partition A ι) (Q : Partition A κ)
    (hc : ∀ i j,P.effect i*Q.effect j=Q.effect j*P.effect i)
    (i k : ι) (j : κ) :
    (P.joint Q hc).effect (i,j)*P.effect k=
      if i=k then (P.joint Q hc).effect (i,j) else 0 := by
  change (P.effect i*Q.effect j)*P.effect k=_
  rw [mul_assoc,← hc,← mul_assoc,P.product]
  split_ifs <;> simp [joint]

theorem joint_right (P : Partition A ι) (Q : Partition A κ)
    (hc : ∀ i j,P.effect i*Q.effect j=Q.effect j*P.effect i)
    (i : ι) (j k : κ) :
    (P.joint Q hc).effect (i,j)*Q.effect k=
      if j=k then (P.joint Q hc).effect (i,j) else 0 := by
  change (P.effect i*Q.effect j)*Q.effect k=_
  rw [mul_assoc,Q.product]
  split_ifs <;> simp [joint]

/-- Real reflections give their two complete spectral projections. True is minus. -/
def reflection [Algebra ℂ A] [StarModule ℂ A]
    (U : A) (hs : star U=U) (hp : U*U=1) : Partition A Bool where
  effect b := (1/2:ℂ) • (1+RowColumns.sign b • U)
  selfadjoint b := by
    simp only [star_smul,star_add,star_one,RowColumns.sign_star,hs]
    norm_num
  product b c := by
    cases b <;> cases c <;>
      norm_num only [RowColumns.sign,Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,
        one_smul,neg_one_smul,Bool.false_eq_true,smul_mul_smul_comm,add_mul,mul_add,
        neg_mul,mul_neg,neg_neg,mul_one,one_mul,hp]
    all_goals module
  total := by
    simp only [Fintype.sum_bool,RowColumns.sign,Bool.false_eq_true,ite_false,ite_true,
      one_smul,neg_one_smul]
    module

end Partition

/-- Operator-matrix projective partitions are genuine complete l2 POVMs. -/
def realizePartition {d : ℕ} [NeZero d] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : Partition (Matrix (Fin d) (Fin d) Op) ι) : Partition Op ι where
  effect i := FiniteAncilla.matrixOp d (P.effect i)
  selfadjoint i := by rw [← FiniteAncilla.matrixOp_star,P.selfadjoint]
  product i j := by
    rw [← FiniteAncilla.matrixOp_mul,P.product]
    split_ifs <;> simp
  total := by
    have he := FiniteAncilla.matrixOp_sum d Finset.univ P.effect
    simpa [P.total] using he.symm

theorem Partition.positive {ι : Type} [Fintype ι] [DecidableEq ι] (P : Partition Op ι) (i : ι) :
    Positive (P.effect i) :=
  ContinuousLinearMap.IsPositive.of_isStarProjection ⟨P.square i,P.selfadjoint i⟩

/-- Finite coarsening preserves vector mirrors term by term. -/
theorem coarse_mirror {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (P Q : Partition Op ι) (v : AB)
    (hm : ∀ i,TensorLifts.left (P.effect i) v=TensorLifts.right (Q.effect i) v)
    (f : ι → κ) (k : κ) :
    TensorLifts.left ((P.coarse f).effect k) v=
      TensorLifts.right ((Q.coarse f).effect k) v := by
  change TensorLifts.left (∑ i,if f i=k then P.effect i else 0) v=
    TensorLifts.right (∑ i,if f i=k then Q.effect i else 0) v
  have hL : TensorLifts.left (∑ i,if f i=k then P.effect i else 0)=
      ∑ i,TensorLifts.left (if f i=k then P.effect i else 0) := by
    simpa using TensorLifts.left_sum Finset.univ (fun i => if f i=k then P.effect i else 0)
  have hR : TensorLifts.right (∑ i,if f i=k then Q.effect i else 0)=
      ∑ i,TensorLifts.right (if f i=k then Q.effect i else 0) := by
    simpa using TensorLifts.right_sum Finset.univ (fun i => if f i=k then Q.effect i else 0)
  rw [hL,hR]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs
  · exact hm i
  · simp only [CoarseCells.left_zero,CoarseCells.right_zero,zero_apply]

/-- Joint mirrors reverse products; Bob's joint commutation restores the order. -/
theorem joint_mirror {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (P P' : Partition Op ι) (Q Q' : Partition Op κ)
    (hc : ∀ i j,P.effect i*Q.effect j=Q.effect j*P.effect i)
    (hc' : ∀ i j,P'.effect i*Q'.effect j=Q'.effect j*P'.effect i)
    (v : AB) (hP : ∀ i,TensorLifts.left (P.effect i) v=TensorLifts.right (P'.effect i) v)
    (hQ : ∀ j,TensorLifts.left (Q.effect j) v=TensorLifts.right (Q'.effect j) v)
    (ij : ι × κ) :
    TensorLifts.left ((P.joint Q hc).effect ij) v=
      TensorLifts.right ((P'.joint Q' hc').effect ij) v := by
  change TensorLifts.left (P.effect ij.1*Q.effect ij.2) v=
    TensorLifts.right (P'.effect ij.1*Q'.effect ij.2) v
  rw [hc' ij.1 ij.2]
  exact FiniteAncilla.product_mirror _ _ _ _ v (hP ij.1) (hQ ij.2)

/-- Binary old-label POVMs synchronize on every original component. -/
theorem binary_mirror (E F : Op) (hE : Projection E) (hF : Projection F)
    (v : AB) (hm : TensorLifts.left E v=TensorLifts.right F v) (b : Bool) :
    TensorLifts.left ((Partition.binary E hE.1 hE.2).effect b) v=
      TensorLifts.right ((Partition.binary F hF.1 hF.2).effect b) v := by
  cases b
  · change TensorLifts.left (1-E) v=TensorLifts.right (1-F) v
    rw [PureSupport.left_sub,MagicRelations.right_sub,TensorLifts.left_one,TensorLifts.right_one]
    change v-TensorLifts.left E v=v-TensorLifts.right F v
    rw [hm]
  · exact hm

end Sigma2.RowCompleteness
