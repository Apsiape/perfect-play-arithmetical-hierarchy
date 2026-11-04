import Sigma2.CalibrationCoefficients

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationGeometry
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients

def phase (y : Fin 2) : ℂ := if y=0 then 1 else -1

/-- The two selected row directions, in the fixed column-zero matrix units. -/
theorem row_direction_formula (e X1 Z1 X2 Z2 : Op) (h : TwoPairs e X1 Z1 X2 Z2) (y : Fin 2) :
    projector e Z1 0*projector e X2 y=
      (1/2:ℂ) • (matrixUnit e X1 Z1 X2 Z2 (0,0) (0,0)+
        matrixUnit e X1 Z1 X2 Z2 (0,1) (0,1)+
        phase y • (matrixUnit e X1 Z1 X2 Z2 (0,0) (0,1)+
          matrixUnit e X1 Z1 X2 Z2 (0,1) (0,0))) := by
  have hd : matrixUnit e X1 Z1 X2 Z2 (0,0) (0,0)+matrixUnit e X1 Z1 X2 Z2 (0,1) (0,1)=
      projector e Z1 0 := by
    simp only [matrixUnit,qubit_diagonal,← mul_add,projector_sum]
    exact (projector_supported e X1 Z1 h.first 0).2
  have ho : matrixUnit e X1 Z1 X2 Z2 (0,0) (0,1)+matrixUnit e X1 Z1 X2 Z2 (0,1) (0,0)=
      projector e Z1 0*X2 := by
    simp only [matrixUnit,qubitUnit,show (0:Fin 2)≠1 from by decide,
      show (1:Fin 2)≠0 from by decide,ite_true,ite_false,← mul_add]
    rw [add_comm (projector e Z2 1),projector_sum,h.second.Xe]
  rw [hd,ho]
  change projector e Z1 0*((1/2:ℂ) • (e+phase y • X2))=_
  rw [mul_smul_comm,mul_add,mul_smul_comm,(PauliMatrixUnits.projector_supported e X1 Z1 h.first 0).2]

def rowDirection {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (y : Fin 2) : Op :=
  P*S.measurements.alice (I.qA 0) (I.aA ⟨y.val+1,by omega⟩)*P

theorem actual_row_direction {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (y : Fin 2) :
    rowDirection S I P y=(1/2:ℂ) •
      (actualUnit S I P 0 0+actualUnit S I P 1 1+
        phase y • (actualUnit S I P 0 1+actualUnit S I P 1 0)) := by
  have hj := joint_projector_outcome (compressed P (rowPOVM S I 0)) P hP.1
    (compressed_positive P hP.1 _ (fun a => S.measurements.alice_pos _ _))
    (compressed_sum P hP.1 _ (hS.2.1 0)) (row_sharp S I hS h hm P hP 0) 0 y
  have hpair : TwoPairs (rowActive S I P 0) (rowCell S I P 1 1) (rowCell S I P 0 0)
      (rowCell S I P 0 1) (rowCell S I P 1 0) := by
    obtain ⟨h1,h2,hxx,hxz,hzx,hzz⟩ := actual_pauli_pairs S I hS h hm P hP
    exact ⟨h1,h2,hxx,hxz,hzx,hzz⟩
  have hh := row_direction_formula _ _ _ _ _ hpair y
  change projector (rowActive S I P 0) (rowCell S I P 0 0) 0*
    projector (rowActive S I P 0) (rowCell S I P 0 1) y=_ at hj
  rw [hj] at hh
  simpa [rowDirection,actualUnit,index,answer,compressed,rowPOVM] using hh

/-- The mirror of Bob's actual sign support is the flag plus the selected
row-zero direction. This uses the original finite forbidden events. -/
theorem bob_sign_sector {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalB (normalOfPure S) h) (Q : Op) (hQ : SupportOf h Q) (y : Fin 2) :
    right (sumB S I y) S.vector=
      left (flagA (normalOfPure S) I+
        S.measurements.alice (I.qA 0) (I.aA ⟨y.val+1,by omega⟩)) S.vector ∧
    sumB S I y*Q=Q*sumB S I y ∧ Projection (Q*sumB S I y*Q) := by
  have hz (b a : Fin 6) (hab : signClassA b≠signClassB y a) :
      (inner ℂ (PureTransfer.flipPure S).vector
        ((left (S.measurements.bob (I.qB (signQuestion y)) (I.aB b))*
          right (S.measurements.alice (I.qA 0) (I.aA a))) (PureTransfer.flipPure S).vector)).re=0 := by
    have hr : conditionalFmsRule 0 (signQuestion y).val a.val b.val=false := by
      fin_cases y <;> fin_cases a <;> fin_cases b <;>
        norm_num [signClassA,signClassB,signQuestion,conditionalFmsRule,fmsRule,retained] at *
    have hh := hS.1 0 (signQuestion y) a b hr
    rw [normalOfPure_probability] at hh
    have he := (PureTransfer.flipPure_probability S (I.qA 0) (I.qB (signQuestion y)) (I.aA a) (I.aB b)).trans hh
    unfold PureStrategy.probability at he
    change (inner ℂ (swap S.vector)
      ((left (S.measurements.bob (I.qB (signQuestion y)) (I.aB b))*
        right (S.measurements.alice (I.qA 0) (I.aA a))) (swap S.vector))).re=0 at he
    exact he
  have hh := coarse_analysis (PureTransfer.flipPure S) h hm Q hQ
    (fun b => S.measurements.bob (I.qB (signQuestion y)) (I.aB b))
    (fun a => S.measurements.alice (I.qA 0) (I.aA a))
    (fun _ => S.measurements.bob_pos _ _) (fun _ => S.measurements.alice_pos _ _)
    (hS.2.2 (signQuestion y)) (hS.2.1 0) signClassA (signClassB y) hz 0
  have hswap := congrArg swap hh.1
  have hmatch : right (sumB S I y) S.vector=
      left (flagA (normalOfPure S) I+S.measurements.alice (I.qA 0) (I.aA ⟨y.val+1,by omega⟩)) S.vector := by
    fin_cases y <;>
      simpa [coarse,signClassA,signClassB,sumB,signQuestion,Fin.sum_univ_succ,
        PureTransfer.flipPure,PureTransfer.swap_left,PureTransfer.swap_right,swap_swap,flagA,normalOfPure] using hswap
  refine ⟨hmatch,?_,?_⟩
  · fin_cases y <;> simpa [coarse,signClassA,sumB,signQuestion,Fin.sum_univ_succ] using hh.2.1
  · fin_cases y <;> simpa [coarse,signClassA,sumB,signQuestion,Fin.sum_univ_succ] using hh.2.2.1

#print axioms actual_row_direction
#print axioms bob_sign_sector
end Sigma2.CalibrationGeometry
