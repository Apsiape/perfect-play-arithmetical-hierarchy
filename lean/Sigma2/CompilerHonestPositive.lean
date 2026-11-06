import Sigma2.CompilerHonestEncoding
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! The one-unitary encoding of supported positive labels, with the exact
identity-on-complement convention of the frozen compiler syntax. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Sigma2.CompilerHonestPositive

local instance : SMul ℝ Op := (Module.restrictScalars ℝ ℂ Op).toSMul
local instance : Module ℝ Op := Module.restrictScalars ℝ ℂ Op
local instance : Algebra ℝ Op := Algebra.restrictScalars ℝ ℂ Op
local instance : NormedSpace ℝ Op := NormedSpace.restrictScalars ℝ ℂ Op
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ Op
local instance : IsScalarTower ℝ ℂ Op where
  smul_assoc r c A := by
    change ((r:ℂ)*c) • A=(r:ℂ) • (c • A)
    exact mul_smul (r:ℂ) c A

theorem centered_contractive (T : Op) (hT : Positive T) (hTc : Positive (1-T)) :
    Contraction ((2:ℂ) • T-1) := by
  have ht : (0:Op)≤T := ContinuousLinearMap.nonneg_iff_isPositive.mpr hT
  have htc : (0:Op)≤1-T := ContinuousLinearMap.nonneg_iff_isPositive.mpr hTc
  have hn : ‖T‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg T ht).mpr (sub_nonneg.mp htc)
  have hsq : Positive (T-T*T) := ContinuousLinearMap.nonneg_iff_isPositive.mp
    (sub_nonneg.mpr (CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one ht hn))
  let A : Op := (2:ℂ) • T-1
  have hs : star A=A := by
    dsimp only [A]
    rw [star_sub ((2:ℂ) • T) 1,star_smul (2:ℂ) T,hT.isSelfAdjoint.star_eq,star_one]
    norm_num
  have he : 1-star A*A=(4:ℂ) • (T-T*T) := by
    rw [hs]
    dsimp [A]
    simp only [sub_mul,mul_sub,smul_mul_smul_comm,smul_mul_assoc,mul_smul_comm,
      one_mul,mul_one]
    module
  have hp : Positive (1-star A*A) := by
    rw [he]
    exact hsq.smul_of_nonneg (by simp [Complex.le_def])
  have hpn : (0:Op)≤star A*A := star_mul_self_nonneg A
  have hnp : ‖star A*A‖≤1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpn).mpr
    (sub_nonneg.mp (ContinuousLinearMap.nonneg_iff_isPositive.mpr hp))
  have hnorm := CStarRing.norm_star_mul_self (x:=A)
  rw [hnorm] at hnp
  change ‖A‖≤1
  nlinarith [norm_nonneg A]

/-- A positive contraction is exactly (2I+U+U*)/4, and the chosen unitary
commutes with every specified density that commutes with the contraction. -/
theorem positive_encoding (h : Density) (T : Op) (hT : Positive T)
    (hTc : Positive (1-T)) (hc : Centralizes h.op T) :
    ∃ U : Op,Unitary U ∧ Centralizes h.op U ∧
      T=(1/4:ℂ) • ((2:ℂ) • (1:Op)+U+star U) := by
  let A : Op := (2:ℂ) • T-1
  have hs : star A=A := by
    dsimp only [A]
    rw [star_sub ((2:ℂ) • T) 1,star_smul (2:ℂ) T,hT.isSelfAdjoint.star_eq,star_one]
    norm_num
  have hsa : IsSelfAdjoint A := hs
  let U : Op := A+Complex.I • CFC.sqrt (1-A^2)
  have hu : Unitary U := hsa.self_add_I_smul_cfcSqrt_sub_sq_mem_unitary A
    (centered_contractive T hT hTc)
  have hca : Commute h.op A :=
    ((show Commute h.op T from hc).smul_right (2:ℂ)).sub_right (Commute.one_right _)
  have hcb : Commute h.op (CFC.sqrt (1-A^2)) := by
    have hh : Commute h.op (1-A^2) := (Commute.one_right _).sub_right (hca.pow_right 2)
    exact (hh.symm.cfcₙ_nnreal NNReal.sqrt).symm
  have hcu : Centralizes h.op U := hca.add_right (hcb.smul_right Complex.I)
  have hsu : star U=A-Complex.I • CFC.sqrt (1-A^2) := by
    have hroot : star (CFC.sqrt (1-A^2))=CFC.sqrt (1-A^2) :=
      (CFC.sqrt_nonneg (1-A^2)).isSelfAdjoint.star_eq
    dsimp only [U]
    rw [star_add A (Complex.I • CFC.sqrt (1-A^2)),star_smul Complex.I _,hs,hroot]
    simp only [Complex.star_def,Complex.conj_I,sub_eq_add_neg]
    module
  refine ⟨U,hu,hcu,?_⟩
  rw [hsu]
  change T=(1/4:ℂ) • ((2:ℂ) • (1:Op)+(A+Complex.I • CFC.sqrt (1-A^2))+
    (A-Complex.I • CFC.sqrt (1-A^2)))
  dsimp [A]
  module

/-- The positive-label encoding fixes the entire ambient complement of the
realization support, as required of each frozen `copyAtom`. -/
theorem supported_positive_encoding (h : Density) (e T : Op)
    (he : Preliminaries.SupportOf h e) (hT : Positive T) (hTc : Positive (e-T))
    (hTe : T*e=T) (heT : e*T=T) (hc : Centralizes h.op T) :
    ∃ U : Op, Unitary U ∧ Centralizes h.op U ∧ (U-1)*(1-e)=0 ∧
      T=e*((1/4:ℂ) • ((2:ℂ) • (1:Op)+U+star U)) := by
  let Q : Op := 1-e
  have hQ : Projection Q := Compiler.projection_compl e he.1
  have hQp : Positive Q := ContinuousLinearMap.IsPositive.of_isStarProjection ⟨hQ.2,hQ.1⟩
  have hct : Positive (1-(T+Q)) := by
    have heq : 1-(T+Q)=e-T := by dsimp [Q]; abel
    rw [heq]
    exact hTc
  have hre : h.op*e=h.op := by
    have hh := congrArg (fun B : Op => star B) he.2.1
    simpa only [star_mul,he.1.1,h.positive.isSelfAdjoint.star_eq] using hh
  have hcQ : Commute h.op Q := by
    change h.op*(1-e)=(1-e)*h.op
    rw [mul_sub,sub_mul,mul_one,one_mul,hre,he.2.1]
  obtain ⟨U,hU,hcU,hm⟩ := positive_encoding h (T+Q) (hT.add hQp) hct
    ((show Commute h.op T from hc).add_right hcQ)
  let D : Op := U-1
  have hsq : star D*D=(4:ℂ) • (1-(T+Q)) := by
    rw [hm]
    dsimp [D]
    rw [star_sub U 1,star_one,sub_mul,mul_sub,mul_sub,hU.1,mul_one,one_mul,one_mul]
    module
  have hz : (1-(T+Q))*Q=0 := by
    dsimp [Q]
    simp only [sub_mul,add_mul,mul_sub,mul_one,one_mul,hTe,he.1.2]
    abel
  have hzD : star D*D*Q=0 := by rw [hsq,smul_mul_assoc,hz]; exact CompilerAlgebra.op_smul_zero _
  have hzz : star (D*Q)*(D*Q)=0 := by
    rw [star_mul,hQ.1]
    calc
      _=Q*(star D*D*Q) := by noncomm_ring
      _=0 := by rw [hzD,mul_zero]
  have hn := CStarRing.norm_star_mul_self (x:=D*Q)
  rw [hzz,norm_zero] at hn
  have hnorm : ‖D*Q‖=0 := by nlinarith [norm_nonneg (D*Q)]
  refine ⟨U,hU,hcU,norm_eq_zero.mp hnorm,?_⟩
  rw [← hm,mul_add,heT]
  have heQ : e*Q=0 := by dsimp [Q]; rw [mul_sub,mul_one,he.1.2,sub_self]
  rw [heQ,add_zero]

#print axioms centered_contractive
#print axioms positive_encoding
#print axioms supported_positive_encoding
end Sigma2.CompilerHonestPositive
