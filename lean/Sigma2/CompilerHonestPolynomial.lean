import Sigma2.CompilerHonestPrerequisites

/-! The frozen polynomial-row coefficients give exactly the qutrit residual,
including the quantitative 2/3 factor. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestPolynomial
open Compiler CompilerScaffold CompilerHonestQutrit CompilerApproxQutrit
  CompilerApproxBlocks FiniteAncilla
abbrev M := Matrix (Fin 3) (Fin 3) Op

@[simp] theorem residual_zero : residualBlocks 0=0 := by
  apply Matrix.ext
  intro i j
  simp [residualBlocks,singleBlocks,star_zero Op]

theorem residual_add (A B : Op) : residualBlocks (A+B)=residualBlocks A+residualBlocks B := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [residualBlocks,singleBlocks,star_add A B]

/-- One term of the literal `polynomialRow`, including its frame subtraction. -/
theorem graph_row_identity (q : ℚ) (A : Op) :
    ((2*q:ℚ):ℂ) • graphBlocks A-(q:ℂ) • pairFrame=residualBlocks ((q:ℂ) • A) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [graphBlocks,pairFrame,residualBlocks,singleBlocks,
      Matrix.smul_apply,Matrix.sub_apply,Matrix.add_apply,star_smul,star_ratCast] <;> module

def rowBlocks (U : ℕ → Op) (p : Poly) : M :=
  (p.map (fun t => ((2*t.1:ℚ):ℂ) • graphBlocks (evalWord U t.2))).sum-
    (((p.map Prod.fst).sum:ℚ):ℂ) • pairFrame

/-- The exact rational row expression in the frozen compiler, before its
Boolean extension, is the residual in the first qutrit pair. -/
theorem rowBlocks_eq (U : ℕ → Op) (p : Poly) :
    rowBlocks U p=residualBlocks (evalPoly U p) := by
  induction p with
  | nil =>
      simp only [rowBlocks,evalPoly,List.map_nil,List.sum_nil,Rat.cast_zero]
      rw [zero_smul ℂ pairFrame,sub_zero,residual_zero]
  | cons t p ih =>
      have hrec : rowBlocks U (t::p)=
          (((2*t.1:ℚ):ℂ) • graphBlocks (evalWord U t.2)-(t.1:ℂ) • pairFrame)+rowBlocks U p := by
        simp only [rowBlocks,List.map_cons,List.sum_cons,Rat.cast_add]
        module
      rw [hrec,graph_row_identity,ih,← residual_add]
      rfl

theorem evalWord_centralizer (h : Density) (U : ℕ → Op)
    (hc : ∀ i,Centralizes h.op (U i)) (w : Word) : Centralizes h.op (evalWord U w) := by
  induction w with
  | nil => simp [evalWord,Centralizes]
  | cons t w ih =>
      have ht : Centralizes h.op (if t.2 then star (U t.1) else U t.1) := by
        split_ifs
        · have hh := congrArg (fun A : Op => star A) (hc t.1)
          rw [star_mul,star_mul,h.positive.isSelfAdjoint.star_eq] at hh
          exact hh.symm
        · exact hc t.1
      exact (show Commute h.op _ from ht).mul_right ih

theorem evalPoly_centralizer (h : Density) (U : ℕ → Op)
    (hc : ∀ i,Centralizes h.op (U i)) (p : Poly) : Centralizes h.op (evalPoly U p) := by
  induction p with
  | nil => simp [evalPoly,Centralizes]
  | cons t p ih =>
      exact ((show Commute h.op _ from evalWord_centralizer h U hc t.2).smul_right
        (t.1:ℂ)).add_right ih

/-- The quantitative energy statement now applies to the actual graph-row
polynomial, with no selfadjointness assumption on the original residual. -/
theorem row_energy (h : Density) (U : ℕ → Op)
    (hc : ∀ i,Centralizes h.op (U i)) (p : Poly) :
    let qh := CompilerHonestDensity.weightedDensity 3 (fun _ => (1/3:ℝ))
      (fun _ => by norm_num) (by norm_num [Fin.sum_univ_three]) h
    (trace (qh.op*(star (matrixOp 3 (rowBlocks U p))*matrixOp 3 (rowBlocks U p)))).re=
      (2/3:ℝ)*(trace (h.op*(star (evalPoly U p)*evalPoly U p))).re := by
  rw [rowBlocks_eq]
  exact qutrit_residual_energy h (evalPoly U p) (evalPoly_centralizer h U hc p)

#print axioms rowBlocks_eq
#print axioms row_energy

/-- Literal interpretation of the named projections occurring in polynomial
rows. Other name constructors do not occur in `polynomialRow`. -/
def polynomialName (U : ℕ → Op) : ProjectionName → Op
  | .graph w 0 0 => matrixOp 3 (graphBlocks (evalWord U w))
  | .frame 0 => matrixOp 3 (singleBlocks 3 0 0 1)
  | .frame 1 => matrixOp 3 (singleBlocks 3 1 1 1)
  | _ => 0

def rowOperator (N : ProjectionName → Op) (r : RationalRow) : Op :=
  (r.constant:ℂ) • (1:Op)+(r.terms.map (fun t => (t.1:ℂ) • N t.2)).sum

theorem matrixOp_list_sum (xs : List M) :
    matrixOp 3 xs.sum=(xs.map (matrixOp 3)).sum := by
  induction xs with
  | nil => exact matrixOp_zero 3
  | cons A xs ih => simp only [List.sum_cons,List.map_cons,matrixOp_add,ih]

theorem matrixOp_sub (A B : M) : matrixOp 3 (A-B)=matrixOp 3 A-matrixOp 3 B := by
  have hn : matrixOp 3 (-B)= -matrixOp 3 B := by
    simpa only [neg_one_smul ℂ B,neg_one_smul ℂ (matrixOp 3 B)] using matrixOp_smul 3 (-1:ℂ) B
  simp only [sub_eq_add_neg,matrixOp_add,hn]

theorem pairFrame_split : pairFrame=singleBlocks 3 0 0 1+singleBlocks 3 1 1 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pairFrame,singleBlocks]

/-- This is the actual frozen `polynomialRow`, with its exact coefficients and
frame terms, rather than an independently chosen replacement row. -/
theorem polynomialRow_operator (U : ℕ → Op) (p : Poly) :
    rowOperator (polynomialName U) (polynomialRow p)=matrixOp 3 (rowBlocks U p) := by
  simp only [polynomialRow,row,rowOperator,List.map_append,List.map_map,Function.comp_def,
    List.map_cons,List.map_nil,List.sum_append,List.sum_cons,List.sum_nil,
    polynomialName,Rat.cast_zero,zero_smul ℂ (1:Op),zero_add]
  rw [rowBlocks,matrixOp_sub,matrixOp_list_sum,matrixOp_smul]
  simp only [List.map_map,Function.comp_def,matrixOp_smul]
  rw [pairFrame_split,matrixOp_add]
  push_cast
  module

#print axioms polynomialRow_operator

end Sigma2.CompilerHonestPolynomial
