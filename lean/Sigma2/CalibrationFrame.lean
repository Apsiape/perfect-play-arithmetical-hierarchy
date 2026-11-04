import Sigma2.CalibrationGeometry

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationFrame
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry

theorem op_smul_zero (c : ℂ) : c • (0:Op)=0 := by
  apply ContinuousLinearMap.ext
  intro z
  ext k
  change c*(0:ℂ)=0
  exact mul_zero c

structure Frame (f : Op) (t : Fin 4 → Fin 4 → Op) : Prop where
  flag : Projection f
  mul : ∀ i j k l,t i j*t k l=if j=k then t i l else 0
  adjoint : ∀ i j,star (t i j)=t j i
  flag_left : ∀ i j,f*t i j=0
  flag_right : ∀ i j,t i j*f=0

theorem actual_frame {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    Frame (P*flagA (normalOfPure S) I*P) (actualUnit S I P) := by
  have hu := units_analysis S I hS h hm P hP
  have hf := (SharpEvents.conditional_flag_sharp S I hS h hm P hP).2.1
  have hq (i j : Fin 4) : rowActive S I P 0*actualUnit S I P i j=actualUnit S I P i j := by
    rw [← hu.2.2.2.2,Finset.sum_mul]
    simp only [hu.1]
    simpa using Finset.sum_ite_eq' Finset.univ i (fun k => actualUnit S I P k j)
  have hfl (i j : Fin 4) : (P*flagA (normalOfPure S) I*P)*actualUnit S I P i j=0 := by
    rw [← hq i j,← mul_assoc,flag_active_orthogonal S I hS h hm P hP,zero_mul]
  refine ⟨hf,hu.1,hu.2.1,hfl,?_⟩
  intro i j
  have hh := congrArg star (hfl j i)
  simpa only [star_mul,hf.1,hu.2.1,show star (0:Op)=0 from star_zero Op] using hh

def up (x : Fin 2) : Fin 4 := ⟨x.val,by omega⟩
def colSupport (f : Op) (t : Fin 4 → Fin 4 → Op) (x : Fin 2) : Op := f+t (up x) (up x)
def rowSupport (f : Op) (t : Fin 4 → Fin 4 → Op) (y : Fin 2) : Op :=
  f+(1/2:ℂ) • (t 0 0+t 1 1+phase y • (t 0 1+t 1 0))
def colEmbed (f : Op) (t : Fin 4 → Fin 4 → Op) (x : Fin 2) : Op := f+t (up x) 0
def invSqrtTwo : ℂ := (Real.sqrt 2:ℂ)/2
def rowEmbed (f : Op) (t : Fin 4 → Fin 4 → Op) (y : Fin 2) : Op :=
  f+invSqrtTwo • (t 0 0+phase y • t 1 0)
def sigma (x y : Fin 2) : ℂ := if x=1 ∧ y=1 then -1 else 1

theorem invSqrtTwo_sq : invSqrtTwo*invSqrtTwo=(1/2:ℂ) := by
  have hh : (Real.sqrt 2:ℂ)*(Real.sqrt 2:ℂ)=2 := by exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ)≤2)
  unfold invSqrtTwo
  calc
    _ = ((Real.sqrt 2:ℂ)*(Real.sqrt 2:ℂ))/4 := by ring
    _ = _ := by rw [hh]; norm_num

theorem invSqrtTwo_star : star invSqrtTwo=invSqrtTwo := by simp [invSqrtTwo]

theorem col_projection (f : Op) (t : Fin 4 → Fin 4 → Op) (h : Frame f t) (x : Fin 2) :
    Projection (colSupport f t x) := by
  constructor
  · simp only [colSupport,op_star_add,h.flag.1,h.adjoint]
  · simp only [colSupport,add_mul,mul_add,h.flag.2,h.flag_left,h.flag_right,h.mul,ite_true]
    abel

theorem col_embed (f : Op) (t : Fin 4 → Fin 4 → Op) (h : Frame f t) (x : Fin 2) :
    star (colEmbed f t x)*colEmbed f t x=colSupport f t 0 ∧
      colEmbed f t x*star (colEmbed f t x)=colSupport f t x := by
  constructor <;>
    simp only [colEmbed,colSupport,op_star_add,h.flag.1,h.adjoint,add_mul,mul_add,h.flag.2,
      h.flag_left,h.flag_right,h.mul,ite_true,up] <;> abel

theorem row_embed (f : Op) (t : Fin 4 → Fin 4 → Op) (h : Frame f t) (y : Fin 2) :
    star (rowEmbed f t y)*rowEmbed f t y=colSupport f t 0 ∧
      rowEmbed f t y*star (rowEmbed f t y)=rowSupport f t y := by
  constructor <;> fin_cases y <;>
    norm_num [rowEmbed,colSupport,rowSupport,phase,op_star_add,op_star_smul,h.flag.1,h.adjoint,
      invSqrtTwo_star,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,
      h.flag.2,h.flag_left,h.flag_right,h.mul,up,invSqrtTwo_sq] <;> module

theorem row_projection (f : Op) (t : Fin 4 → Fin 4 → Op) (h : Frame f t) (y : Fin 2) :
    Projection (rowSupport f t y) := by
  have he := row_embed f t h y
  have hs : rowEmbed f t y*colSupport f t 0=rowEmbed f t y := by
    norm_num [rowEmbed,colSupport,up,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      h.flag.2,h.flag_left,h.flag_right,h.mul,ite_true,smul_zero,add_zero,zero_add]
    exact Or.inr (op_smul_zero (phase y))
  rw [← he.2]
  constructor
  · rw [star_mul,star_star]
  · calc
      _ = rowEmbed f t y*(star (rowEmbed f t y)*rowEmbed f t y)*star (rowEmbed f t y) := by noncomm_ring
      _ = _ := by rw [he.1,hs]

/-- The selected overlaps are exactly sigma_xy/sqrt(2). -/
theorem overlap (f : Op) (t : Fin 4 → Fin 4 → Op) (h : Frame f t) (x y : Fin 2) :
    star (colEmbed f t x)*rowEmbed f t y=f+(sigma x y*invSqrtTwo) • t 0 0 := by
  fin_cases x <;> fin_cases y <;>
    norm_num [colEmbed,rowEmbed,sigma,phase,up,op_star_add,h.flag.1,h.adjoint,
      add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,
      h.flag.2,h.flag_left,h.flag_right,h.mul,PauliExtraction.op_neg_mul,PauliExtraction.op_mul_neg] <;> module

theorem sandwich (f : Op) (t : Fin 4 → Fin 4 → Op) (h : Frame f t) (x y : Fin 2) :
    colSupport f t x*rowSupport f t y*colSupport f t x=
      f+(1/2:ℂ) • t (up x) (up x) := by
  fin_cases x <;> fin_cases y <;>
    norm_num [colSupport,rowSupport,phase,up,add_mul,mul_add,smul_mul_assoc,mul_smul_comm,smul_smul,
      h.flag.2,h.flag_left,h.flag_right,h.mul,PauliExtraction.op_neg_mul,PauliExtraction.op_mul_neg] <;> module

#print axioms actual_frame
#print axioms row_embed
#print axioms overlap
#print axioms sandwich
end Sigma2.CalibrationFrame
