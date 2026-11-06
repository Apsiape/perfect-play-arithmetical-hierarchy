import Sigma2.CompilerHonestFMS
import Sigma2.CompilerScaffold

/-! The four FMS families embedded simultaneously in the frozen seventeen
corners. Every family includes its inactive complementary projection. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestFamilies
open Matrix RowCompleteness
variable {n d : ℕ}

def inclusion (e : Fin n → Fin d) : Matrix (Fin d) (Fin n) ℂ :=
  fun i a => if i=e a then 1 else 0

theorem inclusion_star (e : Fin n → Fin d) : (inclusion e).conjTranspose=(inclusion e).transpose := by
  apply Matrix.ext
  intro a i
  change star (if i=e a then (1:ℂ) else 0)=(if i=e a then 1 else 0)
  split_ifs <;> simp

theorem inclusion_isometry (e : Fin n → Fin d) (he : Function.Injective e) :
    (inclusion e).transpose*inclusion e=1 := by
  apply Matrix.ext
  intro a b
  rw [Matrix.mul_apply,Finset.sum_eq_single (e a)]
  · simp [inclusion,Matrix.transpose_apply,he.eq_iff,Matrix.one_apply]
  · intro i hi hia
    simp [inclusion,Matrix.transpose_apply,hia]
  · simp

def embed (e : Fin n → Fin d) (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  inclusion e*A*(inclusion e).transpose

@[simp] theorem embed_zero (e : Fin n → Fin d) : embed e 0=0 := by simp [embed]

theorem embed_star (e : Fin n → Fin d) (A : Matrix (Fin n) (Fin n) ℂ) :
    star (embed e A)=embed e (star A) := by
  have ht : ((inclusion e).transpose).conjTranspose=inclusion e := by
    rw [← inclusion_star,Matrix.conjTranspose_conjTranspose]
  simp only [embed,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_mul,ht,inclusion_star,Matrix.mul_assoc]

theorem embed_mul (e : Fin n → Fin d) (he : Function.Injective e)
    (A B : Matrix (Fin n) (Fin n) ℂ) : embed e A*embed e B=embed e (A*B) := by
  change (inclusion e*A*(inclusion e).transpose)*(inclusion e*B*(inclusion e).transpose)=_
  calc
    _=inclusion e*(A*((inclusion e).transpose*inclusion e)*B)*(inclusion e).transpose := by
      simp only [Matrix.mul_assoc]
    _=embed e (A*B) := by rw [inclusion_isometry e he]; simp [embed,Matrix.mul_assoc]

theorem embed_add (e : Fin n → Fin d) (A B : Matrix (Fin n) (Fin n) ℂ) :
    embed e (A+B)=embed e A+embed e B := by simp [embed,Matrix.mul_add,Matrix.add_mul]

theorem embed_sum {ι : Type} [Fintype ι] (e : Fin n → Fin d)
    (A : ι → Matrix (Fin n) (Fin n) ℂ) : embed e (∑ a,A a)=∑ a,embed e (A a) := by
  simp [embed,Matrix.mul_sum,Matrix.sum_mul]

/-- Extending a finite projective partition by its inactive support complement. -/
def extend (e : Fin n → Fin d) (he : Function.Injective e)
    (P : Partition (Matrix (Fin n) (Fin n) ℂ) (Fin 6))
    (hz : P.effect 5=0) : Partition (Matrix (Fin d) (Fin d) ℂ) (Fin 6) := by
  let E := embed e (1 : Matrix (Fin n) (Fin n) ℂ)
  let Q := 1-E
  have hEs : star E=E := by dsimp only [E]; rw [embed_star,star_one]
  have hEp : E*E=E := by dsimp only [E]; rw [embed_mul e he,one_mul]
  have hQs : star Q=Q := by dsimp [Q]; rw [star_sub,star_one,hEs]
  have hQp : Q*Q=Q := by dsimp [Q]; simp only [sub_mul,mul_sub,one_mul,mul_one,hEp]; abel
  have hleft (a : Fin 6) : E*embed e (P.effect a)=embed e (P.effect a) := by
    dsimp only [E]; rw [embed_mul e he,one_mul]
  have hright (a : Fin 6) : embed e (P.effect a)*E=embed e (P.effect a) := by
    dsimp only [E]; rw [embed_mul e he,mul_one]
  have hzeroL (a : Fin 6) : Q*embed e (P.effect a)=0 := by dsimp [Q]; rw [sub_mul,one_mul,hleft,sub_self]
  have hzeroR (a : Fin 6) : embed e (P.effect a)*Q=0 := by dsimp [Q]; rw [mul_sub,mul_one,hright,sub_self]
  refine ⟨fun a => embed e (P.effect a)+(if a=5 then Q else 0),?_,?_,?_⟩
  · intro a
    rw [star_add,embed_star,P.selfadjoint]
    split_ifs <;> simp [hQs]
  · intro a b
    rw [add_mul,mul_add,mul_add,embed_mul e he,P.product]
    by_cases ha : a=5 <;> by_cases hb : b=5 <;> by_cases hab : a=b <;>
      simp_all [embed_zero,hzeroL,hzeroR,hQp]
  · rw [Finset.sum_add_distrib,← embed_sum,P.total]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    change E+Q=1
    dsimp [Q]
    abel

/-- Exactly the scalar flag and four magic corners named by bridge g. -/
def position (g : Fin 4) (a : Fin 5) : Fin 17 :=
  if ha : a=0 then
    ⟨CompilerScaffold.cornerIndex g.val,by
      have := g.isLt
      dsimp [CompilerScaffold.cornerIndex]
      split_ifs <;> omega⟩
  else ⟨4*g.val+a.val,by have := g.isLt; have := a.isLt; omega⟩

theorem position_injective (g : Fin 4) : Function.Injective (position g) := by
  intro a b h
  fin_cases g <;> fin_cases a <;> fin_cases b <;>
    norm_num [position,CompilerScaffold.cornerIndex] at *

/-- All four Alice measurement families are partitions on the same register. -/
def alice (g : Fin 4) (x : Fin 5) : Partition (Matrix (Fin 17) (Fin 17) ℂ) (Fin 6) :=
  extend (position g) (position_injective g) (CompilerHonestFMS.alicePartition x) (by
    simp [CompilerHonestFMS.alicePartition,CompilerHonestFMS.alice,
      CompilerHonestFMS.rankOne,CompilerHonestFMS.aliceVector_inactive])

/-- All four Bob families use that same register and the actual answer order. -/
def bob (g : Fin 4) (x : Fin 5) : Partition (Matrix (Fin 17) (Fin 17) ℂ) (Fin 6) :=
  extend (position g) (position_injective g) (CompilerHonestFMS.bobPartition x) (by
    simp [CompilerHonestFMS.bobPartition,CompilerHonestFMS.bob,
      CompilerHonestFMS.rankOne,CompilerHonestFMS.bobVector_inactive])

#print axioms position_injective
#print axioms alice
#print axioms bob
end Sigma2.CompilerHonestFamilies
