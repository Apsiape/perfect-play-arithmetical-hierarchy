import Sigma2.CompilerHonestFamilies

/-! The four scalar FMS families share the exact weighted coefficient matrix
of the seventeen-corner honest state. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestFMSWeights
open Matrix CompilerHonestFamilies CompilerHonestFMS
abbrev M := Matrix (Fin 17) (Fin 17) ℂ

theorem r_cube : r^3=2*r := by
  calc r^3=r^2*r := by ring
       _=2*r := by rw [r_square]

def coefficient : M := Matrix.diagonal (fun i => r^((i.val+3)/4)/11)

def localCoefficient : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal (fun i => if i=0 then 1 else r)

theorem localCoefficient_eq : localCoefficient=CompilerHonestFMS.coefficient := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [localCoefficient,CompilerHonestFMS.coefficient]

theorem coefficient_transpose : coefficient.transpose=coefficient := by simp [coefficient]

theorem local_intertwining (g : Fin 4) :
    coefficient*inclusion (position g)=
      inclusion (position g)*((r^g.val/11) • localCoefficient) := by
  apply Matrix.ext
  intro i a
  simp only [coefficient,Matrix.diagonal_mul,Matrix.mul_smul,localCoefficient,Matrix.smul_apply,Matrix.mul_diagonal]
  by_cases hi : i=position g a
  · subst i
    simp only [inclusion,ite_true,one_mul,mul_one,Matrix.smul_apply]
    fin_cases g <;> fin_cases a <;>
      norm_num [position,CompilerScaffold.cornerIndex] <;> ring_nf
    all_goals norm_num [r_square,r_cube]
    all_goals ring
  · simp [inclusion,hi]

theorem local_intertwining_transpose (g : Fin 4) :
    (inclusion (position g)).transpose*coefficient=
      ((r^g.val/11) • localCoefficient)*(inclusion (position g)).transpose := by
  have hh := congrArg Matrix.transpose (local_intertwining g)
  simpa [Matrix.transpose_mul,coefficient_transpose,Matrix.transpose_smul,localCoefficient] using hh

theorem embed_weighted (g : Fin 4) (A B : Matrix (Fin 5) (Fin 5) ℂ) :
    embed (position g) A*coefficient*embed (position g) B=
      embed (position g) (A*((r^g.val/11) • localCoefficient)*B) := by
  let J := inclusion (position g)
  calc
    _=J*(A*((J.transpose*coefficient)*J)*B)*J.transpose := by
      simp only [embed,J,Matrix.mul_assoc]
    _=J*(A*((J.transpose*J)*((r^g.val/11) • localCoefficient))*B)*J.transpose := by
      rw [Matrix.mul_assoc J.transpose coefficient J,local_intertwining]
      simp only [J,Matrix.mul_assoc]
    _=embed (position g) (A*((r^g.val/11) • localCoefficient)*B) := by
      rw [show J.transpose*J=1 from inclusion_isometry _ (position_injective g)]
      simp [embed,J]

theorem embed_transpose (g : Fin 4) (A : Matrix (Fin 5) (Fin 5) ℂ) :
    (embed (position g) A).transpose=embed (position g) A.transpose := by
  simp [embed,Matrix.transpose_mul,Matrix.mul_assoc]

def active (g : Fin 4) : M := embed (position g) 1

theorem active_coefficient (g : Fin 4) : active g*coefficient=coefficient*active g := by
  change (inclusion (position g)*1*(inclusion (position g)).transpose)*coefficient=
    coefficient*(inclusion (position g)*1*(inclusion (position g)).transpose)
  simp only [Matrix.mul_one]
  rw [Matrix.mul_assoc,local_intertwining_transpose,← Matrix.mul_assoc coefficient,
    local_intertwining]
  simp only [Matrix.mul_assoc]

theorem inactive_weighted_left (g : Fin 4) (A : Matrix (Fin 5) (Fin 5) ℂ) :
    (1-active g)*coefficient*embed (position g) A=0 := by
  have he : active g*embed (position g) A=embed (position g) A := by
    rw [active,embed_mul _ (position_injective g),one_mul]
  have hc : (1-active g)*coefficient=coefficient*(1-active g) := by
    rw [sub_mul,mul_sub,one_mul,mul_one,active_coefficient]
  rw [hc,Matrix.mul_assoc,sub_mul,one_mul,he,sub_self,Matrix.mul_zero]

theorem inactive_weighted_right (g : Fin 4) (A : Matrix (Fin 5) (Fin 5) ℂ) :
    embed (position g) A*coefficient*(1-active g)=0 := by
  have he : embed (position g) A*active g=embed (position g) A := by
    rw [active,embed_mul _ (position_injective g),mul_one]
  have hc : coefficient*(1-active g)=(1-active g)*coefficient := by
    rw [sub_mul,mul_sub,one_mul,mul_one,active_coefficient]
  rw [Matrix.mul_assoc,hc,← Matrix.mul_assoc,mul_sub,mul_one,he,sub_self,Matrix.zero_mul]

theorem alice_effect (g : Fin 4) (x : Fin 5) (a : Fin 6) :
    (CompilerHonestFamilies.alice g x).effect a=
      embed (position g) (CompilerHonestFMS.alice x a)+
        if a=5 then 1-active g else 0 := rfl

theorem bob_effect (g : Fin 4) (y : Fin 5) (b : Fin 6) :
    (CompilerHonestFamilies.bob g y).effect b=
      embed (position g) (CompilerHonestFMS.bob y b)+
        if b=5 then 1-active g else 0 := rfl

/-- Every retained FMS rejection vanishes in the shared seventeen-corner
state, including inactive outcomes and both question orientations. -/
theorem rejection (g : Fin 4) (x y : Fin 5) (a b : Fin 6)
    (h : Compiler.conditionalFmsRule x.val y.val a.val b.val=false) :
    (CompilerHonestFamilies.alice g x).effect a*coefficient*
      ((CompilerHonestFamilies.bob g y).effect b).transpose=0 := by
  have hz := CompilerHonestFMS.rejection x y a b h
  have hz' : embed (position g) (CompilerHonestFMS.alice x a)*coefficient*
      embed (position g) (CompilerHonestFMS.bob y b).transpose=0 := by
    rw [embed_weighted,localCoefficient_eq,Matrix.mul_smul,smul_mul_assoc,hz,smul_zero,embed_zero]
  have hactive : (active g).transpose=active g := by rw [active,embed_transpose,Matrix.transpose_one]
  rw [alice_effect,bob_effect]
  simp only [Matrix.transpose_add,add_mul,mul_add]
  by_cases ha : a=5 <;> by_cases hb : b=5
  · subst a; subst b
    simp [Compiler.conditionalFmsRule] at h
  · simp only [ha] at hz'
    simp only [ha,hb,ite_true,ite_false,Matrix.transpose_zero,Matrix.mul_zero,
      Matrix.zero_mul,add_zero,zero_add]
    rw [embed_transpose,hz',inactive_weighted_left,add_zero]
  · simp only [hb] at hz'
    simp only [ha,hb,ite_true,ite_false,Matrix.transpose_sub,Matrix.transpose_one,
      hactive,Matrix.zero_mul,Matrix.mul_zero,add_zero,zero_add]
    rw [embed_transpose,hz',inactive_weighted_right,add_zero]
  · simp only [ha,hb,ite_false,Matrix.transpose_zero,Matrix.mul_zero,Matrix.zero_mul,
      add_zero,zero_add]
    rw [embed_transpose,hz']

#print axioms local_intertwining
#print axioms rejection
end Sigma2.CompilerHonestFMSWeights
