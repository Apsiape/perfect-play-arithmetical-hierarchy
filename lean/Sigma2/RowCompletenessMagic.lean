import Sigma2.RowCompletenessScalar

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler

/-- A commuting adjacent generator can be moved through the rest of a word. -/
private theorem move (A B C : Op) (h : A*B=B*A) : A*(B*C)=B*(A*C) := by
  rw [← mul_assoc,h,mul_assoc]

private theorem move_neg (A B C : Op) (h : A*B= -(B*A)) :
    A*(B*C)= -(B*(A*C)) := by rw [← mul_assoc,h,PauliExtraction.op_neg_mul,mul_assoc]

private theorem square_word (A C : Op) (h : A*A=1) : A*(A*C)=C := by
  rw [← mul_assoc,h,one_mul]

private theorem op_neg_one_smul (A : Op) : (-1:ℂ) • A= -A := neg_one_smul ℂ A

/-- The real magic square determined by the four fixed axis observables. -/
def magicCells (X1 Z1 X2 Z2 : Op) : Fin 3 → Fin 3 → Op :=
  ![![Z1,X2,Z1*X2],![Z2,X1,Z2*X1],![Z1*Z2,X2*X1,(Z1*Z2)*(X2*X1)]]

/-- The honest square relations, proved from the two Pauli pairs. -/
theorem magicCells_relations (X1 Z1 X2 Z2 : Op)
    (h : FourUnits.TwoPairs 1 X1 Z1 X2 Z2) :
    PauliExtraction.SquareRelations 1 (magicCells X1 Z1 X2 Z2) := by
  have hZZ : Z2*Z1=Z1*Z2 := h.ZZ.eq.symm
  have hXZ : X1*Z1= -(Z1*X1) := h.first.XZ
  have hZX : X2*Z1=Z1*X2 := h.ZX.eq.symm
  have hYZ : X1*Z2=Z2*X1 := h.XZ.eq
  have hXY : X2*Z2= -(Z2*X2) := h.second.XZ
  have hXX : X2*X1=X1*X2 := h.XX.eq.symm
  have nZZ := move Z2 Z1
  have nXZ := move_neg X1 Z1
  have nZX := move X2 Z1
  have nYZ := move X1 Z2
  have nXY := move_neg X2 Z2
  have nXX := move X2 X1
  have sX1 := square_word X1
  have sZ1 := square_word Z1
  have sX2 := square_word X2
  have sZ2 := square_word Z2
  refine ⟨⟨by simp,by simp⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x y; fin_cases x <;> fin_cases y <;> simp [magicCells,star_mul,h.first.starX,h.first.starZ,h.second.starX,h.second.starZ,mul_assoc,PauliExtraction.op_neg_mul,PauliExtraction.op_mul_neg,neg_neg,one_mul,mul_one,hZZ,hXZ,hZX,hYZ,hXY,hXX,nZZ _ hZZ,nXZ _ hXZ,nZX _ hZX,nYZ _ hYZ,nXY _ hXY,nXX _ hXX,h.first.XX,h.first.ZZ,h.second.XX,h.second.ZZ,sX1 _ h.first.XX,sZ1 _ h.first.ZZ,sX2 _ h.second.XX,sZ2 _ h.second.ZZ,op_neg_one_smul]
  · intro x y; simp
  · intro x y; simp
  · intro x y; fin_cases x <;> fin_cases y <;> simp [magicCells,star_mul,h.first.starX,h.first.starZ,h.second.starX,h.second.starZ,mul_assoc,PauliExtraction.op_neg_mul,PauliExtraction.op_mul_neg,neg_neg,one_mul,mul_one,hZZ,hXZ,hZX,hYZ,hXY,hXX,nZZ _ hZZ,nXZ _ hXZ,nZX _ hZX,nYZ _ hYZ,nXY _ hXY,nXX _ hXX,h.first.XX,h.first.ZZ,h.second.XX,h.second.ZZ,sX1 _ h.first.XX,sZ1 _ h.first.ZZ,sX2 _ h.second.XX,sZ2 _ h.second.ZZ,op_neg_one_smul]
  · intro x y z; fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [magicCells,star_mul,h.first.starX,h.first.starZ,h.second.starX,h.second.starZ,mul_assoc,PauliExtraction.op_neg_mul,PauliExtraction.op_mul_neg,neg_neg,one_mul,mul_one,hZZ,hXZ,hZX,hYZ,hXY,hXX,nZZ _ hZZ,nXZ _ hXZ,nZX _ hZX,nYZ _ hYZ,nXY _ hXY,nXX _ hXX,h.first.XX,h.first.ZZ,h.second.XX,h.second.ZZ,sX1 _ h.first.XX,sZ1 _ h.first.ZZ,sX2 _ h.second.XX,sZ2 _ h.second.ZZ,op_neg_one_smul]
  · intro x z y; fin_cases x <;> fin_cases z <;> fin_cases y <;> simp [magicCells,star_mul,h.first.starX,h.first.starZ,h.second.starX,h.second.starZ,mul_assoc,PauliExtraction.op_neg_mul,PauliExtraction.op_mul_neg,neg_neg,one_mul,mul_one,hZZ,hXZ,hZX,hYZ,hXY,hXX,nZZ _ hZZ,nXZ _ hXZ,nZX _ hZX,nYZ _ hYZ,nXY _ hXY,nXX _ hXX,h.first.XX,h.first.ZZ,h.second.XX,h.second.ZZ,sX1 _ h.first.XX,sZ1 _ h.first.ZZ,sX2 _ h.second.XX,sZ2 _ h.second.ZZ,op_neg_one_smul]
  · intro x; fin_cases x <;> simp [magicCells,star_mul,h.first.starX,h.first.starZ,h.second.starX,h.second.starZ,mul_assoc,PauliExtraction.op_neg_mul,PauliExtraction.op_mul_neg,neg_neg,one_mul,mul_one,hZZ,hXZ,hZX,hYZ,hXY,hXX,nZZ _ hZZ,nXZ _ hXZ,nZX _ hZX,nYZ _ hYZ,nXY _ hXY,nXX _ hXX,h.first.XX,h.first.ZZ,h.second.XX,h.second.ZZ,sX1 _ h.first.XX,sZ1 _ h.first.ZZ,sX2 _ h.second.XX,sZ2 _ h.second.ZZ,op_neg_one_smul]
  · intro y; fin_cases y <;> norm_num [magicCells,star_mul,h.first.starX,h.first.starZ,h.second.starX,h.second.starZ,mul_assoc,PauliExtraction.op_neg_mul,PauliExtraction.op_mul_neg,neg_neg,one_mul,mul_one,hZZ,hXZ,hZX,hYZ,hXY,hXX,nZZ _ hZZ,nXZ _ hXZ,nZX _ hZX,nYZ _ hYZ,nXY _ hXY,nXX _ hXX,h.first.XX,h.first.ZZ,h.second.XX,h.second.ZZ,sX1 _ h.first.XX,sZ1 _ h.first.ZZ,sX2 _ h.second.XX,sZ2 _ h.second.ZZ,op_neg_one_smul]

end Sigma2.RowCompleteness
