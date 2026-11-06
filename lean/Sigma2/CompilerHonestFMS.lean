import Sigma2.CompilerBase
import Sigma2.RowCompletenessPartitions

/-! The complete five-dimensional scalar FMS family, in the frozen answer
ordering. Rank-one factorization makes every rejected event a scalar overlap. -/
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestFMS
open Compiler Matrix
abbrev M := Matrix (Fin 5) (Fin 5) ℂ

def r : ℂ := (Real.sqrt 2:ℂ)
@[simp] theorem r_square : r^2=2 := by
  change (Real.sqrt 2:ℂ)^2=2
  exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
@[simp] theorem r_star : star r=r := by simp [r]

def rankOne (v : Fin 5 → ℂ) : M := vecMulVec v v

theorem rankOne_transpose (v : Fin 5 → ℂ) : (rankOne v).transpose=rankOne v :=
  transpose_vecMulVec v v

theorem rankOne_star (v : Fin 5 → ℂ) (hv : ∀ i,star (v i)=v i) :
    star (rankOne v)=rankOne v := by
  ext i j
  simp [rankOne,Matrix.star_apply,vecMulVec_apply,star_mul,hv,mul_comm]

theorem rankOne_zero_product (u v : Fin 5 → ℂ) (D : M)
    (h : u ⬝ᵥ (D *ᵥ v)=0) : rankOne u*D*(rankOne v).transpose=0 := by
  rw [rankOne_transpose]
  change vecMulVec u u*D*vecMulVec v v=0
  rw [mul_assoc,mul_vecMulVec,vecMulVec_mul_vecMulVec,h,zero_smul,vecMulVec_zero]

def aliceVector0 : Fin 6 → Fin 5 → ℂ :=
  ![![1,0,0,0,0],
   ![0,(1/2)*r,(1/2)*r,0,0],
   ![0,(1/2)*r,(-1/2)*r,0,0],
   ![0,0,0,(1/2)*r,(1/2)*r],
   ![0,0,0,(1/2)*r,(-1/2)*r],
   ![0,0,0,0,0]]

def aliceVector1 : Fin 6 → Fin 5 → ℂ :=
  ![![1,0,0,0,0],
   ![0,(1/2)*r,0,(1/2)*r,0],
   ![0,(1/2)*r,0,(-1/2)*r,0],
   ![0,0,(1/2)*r,0,(1/2)*r],
   ![0,0,(1/2)*r,0,(-1/2)*r],
   ![0,0,0,0,0]]

def aliceVector2 : Fin 6 → Fin 5 → ℂ :=
  ![![1,0,0,0,0],
   ![0,(1/2)*r,0,0,(1/2)*r],
   ![0,(1/2)*r,0,0,(-1/2)*r],
   ![0,0,(1/2)*r,(1/2)*r,0],
   ![0,0,(1/2)*r,(-1/2)*r,0],
   ![0,0,0,0,0]]

def aliceVector3 : Fin 6 → Fin 5 → ℂ :=
  ![![(1/2)*r,(1/2)*r,0,0,0],
   ![(1/2)*r,(-1/2)*r,0,0,0],
   ![0,0,1,0,0],
   ![0,0,0,1,0],
   ![0,0,0,0,1],
   ![0,0,0,0,0]]

def aliceVector4 : Fin 6 → Fin 5 → ℂ :=
  ![![(1/2)*r,0,(1/2)*r,0,0],
   ![(1/2)*r,0,(-1/2)*r,0,0],
   ![0,1,0,0,0],
   ![0,0,0,1,0],
   ![0,0,0,0,1],
   ![0,0,0,0,0]]

def aliceVector (x : Fin 5) : Fin 6 → Fin 5 → ℂ :=
  ![aliceVector0,aliceVector1,aliceVector2,aliceVector3,aliceVector4] x

def alice (x : Fin 5) (a : Fin 6) : M := rankOne (aliceVector x a)

def bobVector0 : Fin 6 → Fin 5 → ℂ :=
  ![![1,0,0,0,0],
   ![0,1,0,0,0],
   ![0,0,1,0,0],
   ![0,0,0,1,0],
   ![0,0,0,0,1],
   ![0,0,0,0,0]]

def bobVector1 : Fin 6 → Fin 5 → ℂ :=
  ![![1,0,0,0,0],
   ![0,(1/2),(1/2),(1/2),(1/2)],
   ![0,(1/2),(1/2),(-1/2),(-1/2)],
   ![0,(1/2),(-1/2),(1/2),(-1/2)],
   ![0,(1/2),(-1/2),(-1/2),(1/2)],
   ![0,0,0,0,0]]

def bobVector2 : Fin 6 → Fin 5 → ℂ :=
  ![![1,0,0,0,0],
   ![0,(1/2),(1/2),(1/2),(-1/2)],
   ![0,(1/2),(1/2),(-1/2),(1/2)],
   ![0,(1/2),(-1/2),(1/2),(1/2)],
   ![0,(1/2),(-1/2),(-1/2),(-1/2)],
   ![0,0,0,0,0]]

def bobVector3 : Fin 6 → Fin 5 → ℂ :=
  ![![(1/2)*r,(1/2),(1/2),0,0],
   ![(1/2)*r,(-1/2),(-1/2),0,0],
   ![0,(1/2)*r,(-1/2)*r,0,0],
   ![0,0,0,(1/2)*r,(1/2)*r],
   ![0,0,0,(1/2)*r,(-1/2)*r],
   ![0,0,0,0,0]]

def bobVector4 : Fin 6 → Fin 5 → ℂ :=
  ![![(1/2)*r,(1/2),(-1/2),0,0],
   ![(1/2)*r,(-1/2),(1/2),0,0],
   ![0,(1/2)*r,(1/2)*r,0,0],
   ![0,0,0,(1/2)*r,(1/2)*r],
   ![0,0,0,(1/2)*r,(-1/2)*r],
   ![0,0,0,0,0]]

def bobVector (x : Fin 5) : Fin 6 → Fin 5 → ℂ :=
  ![bobVector0,bobVector1,bobVector2,bobVector3,bobVector4] x

def bob (x : Fin 5) (a : Fin 6) : M := rankOne (bobVector x a)

def coefficient : M :=
  !![1,0,0,0,0;
    0,r,0,0,0;
    0,0,r,0,0;
    0,0,0,r,0;
    0,0,0,0,r]

theorem aliceVector_real (x : Fin 5) (a : Fin 6) (i : Fin 5) :
    star (aliceVector x a i)=aliceVector x a i := by
  fin_cases x <;> fin_cases a <;> fin_cases i <;>
    norm_num [aliceVector,aliceVector0,aliceVector1,aliceVector2,aliceVector3,aliceVector4]

theorem aliceVector_inactive (x : Fin 5) : aliceVector x 5=0 := by
  funext i
  fin_cases x <;> fin_cases i <;> simp [aliceVector,aliceVector0,aliceVector1,aliceVector2,aliceVector3,aliceVector4]

theorem aliceVector_dot (x : Fin 5) (a b : Fin 6) :
    aliceVector x a ⬝ᵥ aliceVector x b=if a=b ∧ a.val<5 then 1 else 0 := by
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    norm_num [aliceVector,aliceVector0,aliceVector1,aliceVector2,aliceVector3,aliceVector4,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem alice_star (x : Fin 5) (a : Fin 6) : star (alice x a)=alice x a := by
  apply rankOne_star
  exact aliceVector_real x a

theorem alice_product (x : Fin 5) (a b : Fin 6) :
    alice x a*alice x b=if a=b then alice x a else 0 := by
  change vecMulVec (aliceVector x a) (aliceVector x a)*
    vecMulVec (aliceVector x b) (aliceVector x b)=_
  rw [vecMulVec_mul_vecMulVec,aliceVector_dot]
  by_cases hab : a=b
  · subst b
    by_cases ha : a.val<5
    · simp [ha,alice,rankOne]
    · have he : a=5 := Fin.ext (by have := a.isLt; omega)
      subst a
      simp [alice,rankOne,aliceVector_inactive]
  · simp [hab]

theorem alice_total (x : Fin 5) : ∑ a,alice x a=1 := by
  apply Matrix.ext
  intro i j
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [alice,rankOne,aliceVector,aliceVector0,aliceVector1,aliceVector2,aliceVector3,aliceVector4,Matrix.vecMulVec_apply,
      Matrix.sum_apply,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

def alicePartition (x : Fin 5) : RowCompleteness.Partition M (Fin 6) where
  effect := alice x
  selfadjoint := alice_star x
  product := alice_product x
  total := alice_total x

theorem bobVector_real (x : Fin 5) (a : Fin 6) (i : Fin 5) :
    star (bobVector x a i)=bobVector x a i := by
  fin_cases x <;> fin_cases a <;> fin_cases i <;>
    norm_num [bobVector,bobVector0,bobVector1,bobVector2,bobVector3,bobVector4]

theorem bobVector_inactive (x : Fin 5) : bobVector x 5=0 := by
  funext i
  fin_cases x <;> fin_cases i <;> simp [bobVector,bobVector0,bobVector1,bobVector2,bobVector3,bobVector4]

theorem bobVector_dot (x : Fin 5) (a b : Fin 6) :
    bobVector x a ⬝ᵥ bobVector x b=if a=b ∧ a.val<5 then 1 else 0 := by
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    norm_num [bobVector,bobVector0,bobVector1,bobVector2,bobVector3,bobVector4,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem bob_star (x : Fin 5) (a : Fin 6) : star (bob x a)=bob x a := by
  apply rankOne_star
  exact bobVector_real x a

theorem bob_product (x : Fin 5) (a b : Fin 6) :
    bob x a*bob x b=if a=b then bob x a else 0 := by
  change vecMulVec (bobVector x a) (bobVector x a)*
    vecMulVec (bobVector x b) (bobVector x b)=_
  rw [vecMulVec_mul_vecMulVec,bobVector_dot]
  by_cases hab : a=b
  · subst b
    by_cases ha : a.val<5
    · simp [ha,bob,rankOne]
    · have he : a=5 := Fin.ext (by have := a.isLt; omega)
      subst a
      simp [bob,rankOne,bobVector_inactive]
  · simp [hab]

theorem bob_total (x : Fin 5) : ∑ a,bob x a=1 := by
  apply Matrix.ext
  intro i j
  fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [bob,rankOne,bobVector,bobVector0,bobVector1,bobVector2,bobVector3,bobVector4,Matrix.vecMulVec_apply,
      Matrix.sum_apply,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

def bobPartition (x : Fin 5) : RowCompleteness.Partition M (Fin 6) where
  effect := bob x
  selfadjoint := bob_star x
  product := bob_product x
  total := bob_total x

theorem overlap_0_0 (a b : Fin 6)
    (h : conditionalFmsRule 0 0 a.val b.val=false) :
    aliceVector0 a ⬝ᵥ (coefficient *ᵥ bobVector0 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector0,bobVector0,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_0_1 (a b : Fin 6)
    (h : conditionalFmsRule 0 1 a.val b.val=false) :
    aliceVector0 a ⬝ᵥ (coefficient *ᵥ bobVector1 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector0,bobVector1,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_0_2 (a b : Fin 6)
    (h : conditionalFmsRule 0 2 a.val b.val=false) :
    aliceVector0 a ⬝ᵥ (coefficient *ᵥ bobVector2 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector0,bobVector2,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_0_3 (a b : Fin 6)
    (h : conditionalFmsRule 0 3 a.val b.val=false) :
    aliceVector0 a ⬝ᵥ (coefficient *ᵥ bobVector3 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector0,bobVector3,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_0_4 (a b : Fin 6)
    (h : conditionalFmsRule 0 4 a.val b.val=false) :
    aliceVector0 a ⬝ᵥ (coefficient *ᵥ bobVector4 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector0,bobVector4,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_1_0 (a b : Fin 6)
    (h : conditionalFmsRule 1 0 a.val b.val=false) :
    aliceVector1 a ⬝ᵥ (coefficient *ᵥ bobVector0 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector1,bobVector0,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_1_1 (a b : Fin 6)
    (h : conditionalFmsRule 1 1 a.val b.val=false) :
    aliceVector1 a ⬝ᵥ (coefficient *ᵥ bobVector1 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector1,bobVector1,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_1_2 (a b : Fin 6)
    (h : conditionalFmsRule 1 2 a.val b.val=false) :
    aliceVector1 a ⬝ᵥ (coefficient *ᵥ bobVector2 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector1,bobVector2,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_1_3 (a b : Fin 6)
    (h : conditionalFmsRule 1 3 a.val b.val=false) :
    aliceVector1 a ⬝ᵥ (coefficient *ᵥ bobVector3 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector1,bobVector3,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_1_4 (a b : Fin 6)
    (h : conditionalFmsRule 1 4 a.val b.val=false) :
    aliceVector1 a ⬝ᵥ (coefficient *ᵥ bobVector4 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector1,bobVector4,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_2_0 (a b : Fin 6)
    (h : conditionalFmsRule 2 0 a.val b.val=false) :
    aliceVector2 a ⬝ᵥ (coefficient *ᵥ bobVector0 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector2,bobVector0,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_2_1 (a b : Fin 6)
    (h : conditionalFmsRule 2 1 a.val b.val=false) :
    aliceVector2 a ⬝ᵥ (coefficient *ᵥ bobVector1 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector2,bobVector1,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_2_2 (a b : Fin 6)
    (h : conditionalFmsRule 2 2 a.val b.val=false) :
    aliceVector2 a ⬝ᵥ (coefficient *ᵥ bobVector2 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector2,bobVector2,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_2_3 (a b : Fin 6)
    (h : conditionalFmsRule 2 3 a.val b.val=false) :
    aliceVector2 a ⬝ᵥ (coefficient *ᵥ bobVector3 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector2,bobVector3,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_2_4 (a b : Fin 6)
    (h : conditionalFmsRule 2 4 a.val b.val=false) :
    aliceVector2 a ⬝ᵥ (coefficient *ᵥ bobVector4 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector2,bobVector4,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_3_0 (a b : Fin 6)
    (h : conditionalFmsRule 3 0 a.val b.val=false) :
    aliceVector3 a ⬝ᵥ (coefficient *ᵥ bobVector0 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector3,bobVector0,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_3_1 (a b : Fin 6)
    (h : conditionalFmsRule 3 1 a.val b.val=false) :
    aliceVector3 a ⬝ᵥ (coefficient *ᵥ bobVector1 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector3,bobVector1,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_3_2 (a b : Fin 6)
    (h : conditionalFmsRule 3 2 a.val b.val=false) :
    aliceVector3 a ⬝ᵥ (coefficient *ᵥ bobVector2 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector3,bobVector2,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_3_3 (a b : Fin 6)
    (h : conditionalFmsRule 3 3 a.val b.val=false) :
    aliceVector3 a ⬝ᵥ (coefficient *ᵥ bobVector3 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector3,bobVector3,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_3_4 (a b : Fin 6)
    (h : conditionalFmsRule 3 4 a.val b.val=false) :
    aliceVector3 a ⬝ᵥ (coefficient *ᵥ bobVector4 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector3,bobVector4,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_4_0 (a b : Fin 6)
    (h : conditionalFmsRule 4 0 a.val b.val=false) :
    aliceVector4 a ⬝ᵥ (coefficient *ᵥ bobVector0 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector4,bobVector0,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_4_1 (a b : Fin 6)
    (h : conditionalFmsRule 4 1 a.val b.val=false) :
    aliceVector4 a ⬝ᵥ (coefficient *ᵥ bobVector1 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector4,bobVector1,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_4_2 (a b : Fin 6)
    (h : conditionalFmsRule 4 2 a.val b.val=false) :
    aliceVector4 a ⬝ᵥ (coefficient *ᵥ bobVector2 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector4,bobVector2,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_4_3 (a b : Fin 6)
    (h : conditionalFmsRule 4 3 a.val b.val=false) :
    aliceVector4 a ⬝ᵥ (coefficient *ᵥ bobVector3 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector4,bobVector3,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap_4_4 (a b : Fin 6)
    (h : conditionalFmsRule 4 4 a.val b.val=false) :
    aliceVector4 a ⬝ᵥ (coefficient *ᵥ bobVector4 b)=0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [conditionalFmsRule,fmsRule,cellSign,retained] at h
  all_goals norm_num [aliceVector4,bobVector4,coefficient,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

theorem overlap (x y : Fin 5) (a b : Fin 6)
    (h : conditionalFmsRule x.val y.val a.val b.val=false) :
    aliceVector x a ⬝ᵥ (coefficient *ᵥ bobVector y b)=0 := by
  fin_cases x <;> fin_cases y
  · exact overlap_0_0 a b h
  · exact overlap_0_1 a b h
  · exact overlap_0_2 a b h
  · exact overlap_0_3 a b h
  · exact overlap_0_4 a b h
  · exact overlap_1_0 a b h
  · exact overlap_1_1 a b h
  · exact overlap_1_2 a b h
  · exact overlap_1_3 a b h
  · exact overlap_1_4 a b h
  · exact overlap_2_0 a b h
  · exact overlap_2_1 a b h
  · exact overlap_2_2 a b h
  · exact overlap_2_3 a b h
  · exact overlap_2_4 a b h
  · exact overlap_3_0 a b h
  · exact overlap_3_1 a b h
  · exact overlap_3_2 a b h
  · exact overlap_3_3 a b h
  · exact overlap_3_4 a b h
  · exact overlap_4_0 a b h
  · exact overlap_4_1 a b h
  · exact overlap_4_2 a b h
  · exact overlap_4_3 a b h
  · exact overlap_4_4 a b h

/-- All 474 actual scalar FMS rejections annihilate the same weighted
coefficient matrix, including both orientations and the inactive outcomes. -/
theorem rejection (x y : Fin 5) (a b : Fin 6)
    (h : conditionalFmsRule x.val y.val a.val b.val=false) :
    alice x a*coefficient*(bob y b).transpose=0 :=
  rankOne_zero_product _ _ _ (overlap x y a b h)

def parameter (k : Fin 2) : M :=
  ![!![0,0,0,0,0;
    0,(1/2),0,(1/2),0;
    0,0,(1/2),0,(1/2);
    0,(1/2),0,(1/2),0;
    0,0,(1/2),0,(1/2)],
   !![0,0,0,0,0;
    0,(1/2),(1/2),0,0;
    0,(1/2),(1/2),0,0;
    0,0,0,(1/2),(1/2);
    0,0,0,(1/2),(1/2)]] k

def magic : M :=
  !![0,0,0,0,0;
    0,1,0,0,0;
    0,0,1,0,0;
    0,0,0,1,0;
    0,0,0,0,1]

/-- The frozen alice positive-axis coarse events have the chosen sign. -/
theorem alice_axis_binding (k : Fin 2) :
    (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧
      cellSign false (a.val-1) 1=false then alice (if k=0 then 1 else 0) a else 0)=parameter k := by
  apply Matrix.ext
  intro i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [parameter,alice,rankOne,aliceVector,aliceVector0,aliceVector1,aliceVector2,aliceVector3,aliceVector4,cellSign,
      Matrix.sum_apply,Matrix.vecMulVec_apply,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

/-- The frozen bob positive-axis coarse events have the chosen sign. -/
theorem bob_axis_binding (k : Fin 2) :
    (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧
      cellSign false (a.val-1) (if k=0 then 1 else 0)=false then bob 1 a else 0)=parameter k := by
  apply Matrix.ext
  intro i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [parameter,bob,rankOne,bobVector,bobVector0,bobVector1,bobVector2,bobVector3,bobVector4,cellSign,
      Matrix.sum_apply,Matrix.vecMulVec_apply,Fin.sum_univ_succ]
  all_goals ring_nf
  all_goals simp only [r_square]
  all_goals norm_num

#print axioms alice_product
#print axioms bob_product
#print axioms rejection
#print axioms alice_axis_binding
#print axioms bob_axis_binding
end Sigma2.CompilerHonestFMS
