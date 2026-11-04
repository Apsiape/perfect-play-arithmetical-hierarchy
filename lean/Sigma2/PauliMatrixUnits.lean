import Sigma2.PauliExtraction
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.PauliMatrixUnits
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral MagicCells MagicRelations PauliExtraction

structure Pair (e X Z : Op) : Prop where
  projection : Projection e
  starX : star X=X
  starZ : star Z=Z
  Xe : X*e=X
  eX : e*X=X
  Ze : Z*e=Z
  eZ : e*Z=Z
  XX : X*X=e
  ZZ : Z*Z=e
  XZ : X*Z= -(Z*X)

/-- All six Pauli (anti)commutation relations, with corner unitarity,
are extracted from the original conditional strategy. -/
theorem actual_pauli_pairs {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    let e := rowActive S I P 0
    let C := rowCell S I P
    Pair e (C 1 1) (C 0 0) ∧ Pair e (C 0 1) (C 1 0) ∧
      C 1 1*C 0 1=C 0 1*C 1 1 ∧ C 1 1*C 1 0=C 1 0*C 1 1 ∧
      C 0 0*C 0 1=C 0 1*C 0 0 ∧ C 0 0*C 1 0=C 1 0*C 0 0 := by
  have r := actual_relations S I hS h hm P hP
  have ha := anticommute _ _ r
  refine ⟨?_,?_,r.col_commute 1 0 1,r.row_commute 1 1 0,r.row_commute 0 0 1,r.col_commute 0 1 0⟩
  · refine ⟨r.projection,r.selfadjoint 1 1,r.selfadjoint 0 0,r.right_unit 1 1,r.left_unit 1 1,
      r.right_unit 0 0,r.left_unit 0 0,r.square 1 1,r.square 0 0,?_⟩
    rw [ha.1,neg_neg]
  · exact ⟨r.projection,r.selfadjoint 0 1,r.selfadjoint 1 0,r.right_unit 0 1,r.left_unit 0 1,
      r.right_unit 1 0,r.left_unit 1 0,r.square 0 1,r.square 1 0,ha.2⟩

def projector (e Z : Op) (a : Fin 2) : Op :=
  (1/2:ℂ) • (e+(if a=0 then (1:ℂ) else -1) • Z)

def flip (a : Fin 2) : Fin 2 := if a=0 then 1 else 0

theorem flip_flip (a : Fin 2) : flip (flip a)=a := by fin_cases a <;> decide

theorem projector_mul (e X Z : Op) (h : Pair e X Z) (a b : Fin 2) :
    projector e Z a*projector e Z b=if a=b then projector e Z a else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [projector,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,smul_smul,
      h.projection.2,h.eZ,h.Ze,h.ZZ] <;> module

theorem op_star_add (A B : Op) : star (A+B)=star A+star B := star_add A B

theorem op_star_smul (c : ℂ) (A : Op) : star (c • A)=star c • star A := star_smul c A

theorem projector_star (e X Z : Op) (h : Pair e X Z) (a : Fin 2) :
    star (projector e Z a)=projector e Z a := by
  unfold projector
  rw [op_star_smul,op_star_add,op_star_smul,h.projection.1,h.starZ]
  fin_cases a <;> norm_num

theorem projector_sum (e Z : Op) : projector e Z 0+projector e Z 1=e := by
  norm_num [projector]
  module

theorem projector_supported (e X Z : Op) (h : Pair e X Z) (a : Fin 2) :
    e*projector e Z a=projector e Z a ∧ projector e Z a*e=projector e Z a := by
  fin_cases a <;> constructor <;>
    norm_num [projector,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,h.projection.2,h.eZ,h.Ze]

theorem flip_projector (e X Z : Op) (h : Pair e X Z) (a : Fin 2) :
    X*projector e Z a=projector e Z (flip a)*X := by
  have hz : Z*X= -(X*Z) := by rw [h.XZ,neg_neg]
  fin_cases a <;> norm_num [projector,flip,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,h.Xe,h.eX,hz] <;> module

def qubitUnit (e X Z : Op) (a b : Fin 2) : Op :=
  if a=b then projector e Z b else X*projector e Z b

#print axioms actual_pauli_pairs
#print axioms projector_mul
#print axioms flip_projector
end Sigma2.PauliMatrixUnits
