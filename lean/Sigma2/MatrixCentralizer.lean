import Sigma2.FourUnits
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.MatrixCentralizer
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits

theorem support_centralizes (h : Density) (P : Op) (hP : SupportOf h P) : Commute h.op P := by
  have hh := congrArg star hP.2.1
  have hr : h.op*P=h.op := by simpa only [star_mul,hP.1.1,h.positive.isSelfAdjoint.star_eq] using hh
  exact hr.trans hP.2.1.symm

theorem cells_centralize {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (x y : Fin 3) :
    Commute h.op (rowCell S I P x y) := by
  have hp := support_centralizes h P hP
  have he1 : Commute h.op (rowEffect S I x y 1) := (conditional_cells S I hS h hm P hP x y 1).2.2.2
  have he2 : Commute h.op (rowEffect S I x y 2) := (conditional_cells S I hS h hm P hP x y 2).2.2.2
  change Commute h.op (coarse (compressed P (rowPOVM S I x)) (cellClass false y) 1-
    coarse (compressed P (rowPOVM S I x)) (cellClass false y) 2)
  rw [coarse_compressed,coarse_compressed]
  exact ((hp.mul_right he1).mul_right hp).sub_right ((hp.mul_right he2).mul_right hp)

theorem actual_units_centralize {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (i j : Index) :
    Commute h.op (matrixUnit (rowActive S I P 0) (rowCell S I P 1 1) (rowCell S I P 0 0)
      (rowCell S I P 0 1) (rowCell S I P 1 0) i j) := by
  have hc := cells_centralize S I hS h hm P hP
  have he : Commute h.op (rowActive S I P 0) := by
    rw [← row_square S I hS h hm P hP 0 0]
    exact (hc 0 0).mul_right (hc 0 0)
  exact (commute_unit _ _ _ _ he (hc 1 1) (hc 0 0) i.1 j.1).mul_right
    (commute_unit _ _ _ _ he (hc 0 1) (hc 1 0) i.2 j.2)

theorem qubit_formula (e X Z : Op) (a b : Fin 2) :
    qubitUnit e X Z a b=X^((a.val+b.val)%2)*projector e Z b := by
  fin_cases a <;> fin_cases b <;> norm_num [qubitUnit]

theorem matrix_formula (e X1 Z1 X2 Z2 : Op) (h : TwoPairs e X1 Z1 X2 Z2) (i j : Index) :
    matrixUnit e X1 Z1 X2 Z2 i j=
      X1^((i.1.val+j.1.val)%2)*X2^((i.2.val+j.2.val)%2)*diagonal e Z1 Z2 j := by
  have hc := (commute_projector X2 e Z1 (h.second.Xe.trans h.second.eX.symm) h.ZX.symm j.1).symm
  have hpow := hc.pow_right ((i.2.val+j.2.val)%2)
  unfold matrixUnit diagonal
  rw [qubit_formula,qubit_formula]
  calc
    _ = X1^((i.1.val+j.1.val)%2)*
        (projector e Z1 j.1*X2^((i.2.val+j.2.val)%2))*projector e Z2 j.2 := by noncomm_ring
    _ = _ := by rw [hpow.eq]; noncomm_ring

#print axioms actual_units_centralize
#print axioms matrix_formula
end Sigma2.MatrixCentralizer
