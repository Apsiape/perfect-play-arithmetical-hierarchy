import Sigma2.CompilerHonestCentralizer

/-! A kernel-decided rational certificate for the eight finite positive-axis
matrices. The subsequent cast to complex matrices is purely algebraic. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestAxisCertificate
open CompilerHonestFamilies CompilerFiniteRegister

def parameter (k : Fin 2) : Matrix (Fin 5) (Fin 5) ℚ :=
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

def inclusionQ (g : Fin 4) : Matrix (Fin 17) (Fin 5) ℚ :=
  fun i a => if i=position g a then 1 else 0

def permutationQ (g : Fin 4) (k : Fin 2) : Matrix (Fin 17) (Fin 17) ℚ :=
  fun i j => if j=axisPerm g k i then 1 else 0

def magicQ (g : Fin 4) : Matrix (Fin 17) (Fin 17) ℚ :=
  Matrix.diagonal (fun i => if magicActive g i then 1 else 0)

set_option maxHeartbeats 1000000 in
theorem certificate_0_0 :
    inclusionQ 0*parameter 0*(inclusionQ 0).transpose=
      magicQ 0*((1/2:ℚ) • (1+permutationQ 0 0)) := by
  apply Matrix.ext
  intro i j
  simp only [magicQ,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [inclusionQ,parameter,permutationQ,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,position,CompilerScaffold.cornerIndex,axisPerm,magicIndex,
      magicActive,Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
theorem certificate_0_1 :
    inclusionQ 0*parameter 1*(inclusionQ 0).transpose=
      magicQ 0*((1/2:ℚ) • (1+permutationQ 0 1)) := by
  apply Matrix.ext
  intro i j
  simp only [magicQ,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [inclusionQ,parameter,permutationQ,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,position,CompilerScaffold.cornerIndex,axisPerm,magicIndex,
      magicActive,Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
theorem certificate_1_0 :
    inclusionQ 1*parameter 0*(inclusionQ 1).transpose=
      magicQ 1*((1/2:ℚ) • (1+permutationQ 1 0)) := by
  apply Matrix.ext
  intro i j
  simp only [magicQ,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [inclusionQ,parameter,permutationQ,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,position,CompilerScaffold.cornerIndex,axisPerm,magicIndex,
      magicActive,Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
theorem certificate_1_1 :
    inclusionQ 1*parameter 1*(inclusionQ 1).transpose=
      magicQ 1*((1/2:ℚ) • (1+permutationQ 1 1)) := by
  apply Matrix.ext
  intro i j
  simp only [magicQ,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [inclusionQ,parameter,permutationQ,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,position,CompilerScaffold.cornerIndex,axisPerm,magicIndex,
      magicActive,Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
theorem certificate_2_0 :
    inclusionQ 2*parameter 0*(inclusionQ 2).transpose=
      magicQ 2*((1/2:ℚ) • (1+permutationQ 2 0)) := by
  apply Matrix.ext
  intro i j
  simp only [magicQ,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [inclusionQ,parameter,permutationQ,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,position,CompilerScaffold.cornerIndex,axisPerm,magicIndex,
      magicActive,Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
theorem certificate_2_1 :
    inclusionQ 2*parameter 1*(inclusionQ 2).transpose=
      magicQ 2*((1/2:ℚ) • (1+permutationQ 2 1)) := by
  apply Matrix.ext
  intro i j
  simp only [magicQ,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [inclusionQ,parameter,permutationQ,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,position,CompilerScaffold.cornerIndex,axisPerm,magicIndex,
      magicActive,Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
theorem certificate_3_0 :
    inclusionQ 3*parameter 0*(inclusionQ 3).transpose=
      magicQ 3*((1/2:ℚ) • (1+permutationQ 3 0)) := by
  apply Matrix.ext
  intro i j
  simp only [magicQ,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [inclusionQ,parameter,permutationQ,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,position,CompilerScaffold.cornerIndex,axisPerm,magicIndex,
      magicActive,Equiv.swap_apply_def]

set_option maxHeartbeats 1000000 in
theorem certificate_3_1 :
    inclusionQ 3*parameter 1*(inclusionQ 3).transpose=
      magicQ 3*((1/2:ℚ) • (1+permutationQ 3 1)) := by
  apply Matrix.ext
  intro i j
  simp only [magicQ,Matrix.diagonal_mul,Matrix.smul_apply,Matrix.add_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [inclusionQ,parameter,permutationQ,Matrix.mul_apply,Fin.sum_univ_succ,
      Matrix.one_apply,position,CompilerScaffold.cornerIndex,axisPerm,magicIndex,
      magicActive,Equiv.swap_apply_def]

theorem certificate (g : Fin 4) (k : Fin 2) :
    inclusionQ g*parameter k*(inclusionQ g).transpose=
      magicQ g*((1/2:ℚ) • (1+permutationQ g k)) := by
  fin_cases g <;> fin_cases k
  · exact certificate_0_0
  · exact certificate_0_1
  · exact certificate_1_0
  · exact certificate_1_1
  · exact certificate_2_0
  · exact certificate_2_1
  · exact certificate_3_0
  · exact certificate_3_1

def ratMatrix {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) : Matrix (Fin n) (Fin m) ℂ :=
  fun i j => (A i j:ℂ)

theorem ratMatrix_mul {n m d : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (B : Matrix (Fin m) (Fin d) ℚ) : ratMatrix (A*B)=ratMatrix A*ratMatrix B := by
  apply Matrix.ext
  intro i j
  simp only [ratMatrix,Matrix.mul_apply]
  push_cast
  rfl

theorem ratMatrix_transpose {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℚ) :
    ratMatrix A.transpose=(ratMatrix A).transpose := rfl

theorem ratMatrix_smul {n m : ℕ} (c : ℚ) (A : Matrix (Fin n) (Fin m) ℚ) :
    ratMatrix (c • A)=(c:ℂ) • ratMatrix A := by
  apply Matrix.ext
  intro i j
  exact Rat.cast_mul _ _

theorem ratMatrix_add {n m : ℕ} (A B : Matrix (Fin n) (Fin m) ℚ) :
    ratMatrix (A+B)=ratMatrix A+ratMatrix B := by
  apply Matrix.ext
  intro i j
  exact Rat.cast_add _ _

theorem ratMatrix_one (n : ℕ) : ratMatrix (1 : Matrix (Fin n) (Fin n) ℚ)=1 := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j <;> simp [ratMatrix,Matrix.one_apply,hij]

theorem cast_parameter (k : Fin 2) : ratMatrix (parameter k)=CompilerHonestFMS.parameter k := by
  apply Matrix.ext
  intro i j
  fin_cases k <;> fin_cases i <;> fin_cases j <;>
    norm_num [ratMatrix,parameter,CompilerHonestFMS.parameter]

theorem cast_inclusion (g : Fin 4) : ratMatrix (inclusionQ g)=inclusion (position g) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=position g j <;> simp [ratMatrix,inclusionQ,inclusion,hij]

theorem cast_permutation (g : Fin 4) (k : Fin 2) :
    ratMatrix (permutationQ g k)=(fun i j => if j=axisPerm g k i then (1:ℂ) else 0) := by
  apply Matrix.ext
  intro i j
  by_cases hij : j=axisPerm g k i <;> simp [ratMatrix,permutationQ,hij]

theorem cast_magic (g : Fin 4) :
    ratMatrix (magicQ g)=Matrix.diagonal (fun i => if magicActive g i then (1:ℂ) else 0) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    by_cases hi : magicActive g i <;> simp [ratMatrix,magicQ,hi]
  · simp [ratMatrix,magicQ,Matrix.diagonal_apply,hij]

#print axioms certificate
end Sigma2.CompilerHonestAxisCertificate
