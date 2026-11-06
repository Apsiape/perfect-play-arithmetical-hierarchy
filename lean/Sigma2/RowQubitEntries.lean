import Sigma2.RowEntryCoordinates
import Sigma2.RowColumns

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open PauliMatrixUnits QubitUnits FourUnits Compiler RowGame Preliminaries

/-- The certified measured X is exactly the sum of the two transition units. -/
theorem qubit_X_entries (P X Z : Op) (h : Pair P X Z) :
    X=qubitUnit P X Z 0 1+qubitUnit P X Z 1 0 := by
  simp only [qubitUnit,show (0:Fin 2)≠1 by decide,show (1:Fin 2)≠0 by decide,ite_false]
  rw [← mul_add,add_comm (projector P Z 1),projector_sum,h.Xe]

/-- The measured Z is the difference of its two diagonal units. -/
theorem qubit_Z_entries (P X Z : Op) :
    Z=qubitUnit P X Z 0 0-qubitUnit P X Z 1 1 := by
  simp only [qubit_diagonal,projector,ite_true,show (1:Fin 2)≠0 by decide,ite_false,
    one_smul,neg_one_smul]
  module

theorem qubit_X_action (P X Z : Op) (h : Pair P X Z) (a b : Fin 2) :
    X*qubitUnit P X Z a b=qubitUnit P X Z (PauliMatrixUnits.flip a) b := by
  conv_lhs => lhs; rw [qubit_X_entries P X Z h]
  rw [add_mul,qubit_product P X Z h,qubit_product P X Z h]
  fin_cases a <;> simp [PauliMatrixUnits.flip]

theorem qubit_Z_action (P X Z : Op) (h : Pair P X Z) (a b : Fin 2) :
    Z*qubitUnit P X Z a b=RowColumns.sign (decide (a.val=1)) • qubitUnit P X Z a b := by
  conv_lhs => lhs; rw [qubit_Z_entries P X Z]
  rw [sub_mul,qubit_product P X Z h,qubit_product P X Z h]
  fin_cases a <;> norm_num [RowColumns.sign] <;> module

def indexFlip (i : Index) (k : Fin 2) : Index :=
  if k=0 then (PauliMatrixUnits.flip i.1,i.2) else (i.1,PauliMatrixUnits.flip i.2)

def indexBit (i : Index) (k : Fin 2) : Bool :=
  decide ((if k=0 then i.1 else i.2).val=1)

/-- Entrywise action of the four generators of the certified scalar square. -/
theorem four_axis_action (P X1 Z1 X2 Z2 : Op) (h : TwoPairs P X1 Z1 X2 Z2)
    (isX : Bool) (k : Fin 2) (i j : Index) :
    (if isX then (if k=0 then X1 else X2) else (if k=0 then Z1 else Z2))*
        matrixUnit P X1 Z1 X2 Z2 i j=
      if isX then matrixUnit P X1 Z1 X2 Z2 (indexFlip i k) j
        else RowColumns.sign (indexBit i k) • matrixUnit P X1 Z1 X2 Z2 i j := by
  have he : Commute P (qubitUnit P X1 Z1 i.1 j.1) :=
    commute_unit P P X1 Z1 (Commute.refl P)
      (h.first.eX.trans h.first.Xe.symm) (h.first.eZ.trans h.first.Ze.symm) i.1 j.1
  have hx : Commute X2 (qubitUnit P X1 Z1 i.1 j.1) :=
    commute_unit X2 P X1 Z1 (h.second.Xe.trans h.second.eX.symm) h.XX.symm h.ZX.symm i.1 j.1
  have hz : Commute Z2 (qubitUnit P X1 Z1 i.1 j.1) :=
    commute_unit Z2 P X1 Z1 (h.second.Ze.trans h.second.eZ.symm) h.XZ.symm h.ZZ.symm i.1 j.1
  cases isX <;> fin_cases k
  · norm_num [indexBit,matrixUnit]
    rw [← mul_assoc,qubit_Z_action P X1 Z1 h.first,smul_mul_assoc]
  · norm_num [indexBit,matrixUnit]
    rw [← mul_assoc,hz.eq,mul_assoc,qubit_Z_action P X2 Z2 h.second,mul_smul_comm]
  · norm_num [indexFlip,matrixUnit]
    rw [← mul_assoc,qubit_X_action P X1 Z1 h.first]
  · norm_num [indexFlip,matrixUnit]
    rw [← mul_assoc,hx.eq,mul_assoc,qubit_X_action P X2 Z2 h.second]

/-- The action is for the actual synchronized scalar cells of the original
    perfect strategy, in its existing localUnit coordinates. -/
theorem measured_axis_local_action (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) (isX : Bool) (k : Fin 2) (i j : Index) :
    binary G R S.measurements P (axisQ R g (globalAxis isX k))*localUnit G R S.measurements P g i j=
      if isX then localUnit G R S.measurements P g (indexFlip i k) j
        else RowColumns.sign (indexBit i k) • localUnit G R S.measurements P g i j := by
  have hh := four_axis_action P _ _ _ _ (measured_pauli_pairs G R S hS h hm P hP g) isX k i j
  cases isX <;> fin_cases k <;> simpa [globalAxis,localUnit] using hh

#print axioms qubit_X_entries
#print axioms qubit_Z_entries
#print axioms qubit_X_action
#print axioms qubit_Z_action
#print axioms four_axis_action
#print axioms measured_axis_local_action
end Sigma2.RowScalar

