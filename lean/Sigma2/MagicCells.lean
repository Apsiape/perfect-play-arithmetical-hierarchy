import Sigma2.FiniteSpectral
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.MagicCells
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral

def rowPOVM {s} (S : PureStrategy s) (I : FMSInstance s) (x : Fin 3) : Fin 6 → Op :=
  fun a => S.measurements.alice (I.qA ⟨x.val,by omega⟩) (I.aA a)

def colPOVM {s} (S : PureStrategy s) (I : FMSInstance s) (y : Fin 3) : Fin 6 → Op :=
  fun b => S.measurements.bob (I.qB ⟨y.val,by omega⟩) (I.aB b)

def rowCell {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (x y : Fin 3) : Op :=
  signed (compressed P (rowPOVM S I x)) (cellClass false y)

def rowActive {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (x : Fin 3) : Op :=
  active (compressed P (rowPOVM S I x))

theorem row_sharp {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x y : Fin 3) (t : Fin 4) :
    Projection (coarse (compressed P (rowPOVM S I x)) (cellClass false y) t) := by
  rw [coarse_compressed]
  exact (conditional_cells S I hS h hm P hP x y t).2.2.1

theorem row_commute {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x y z : Fin 3) : rowCell S I P x y*rowCell S I P x z=rowCell S I P x z*rowCell S I P x y := by
  apply signed_commute _ _ _ P hP.1
    (compressed_positive P hP.1 _ (fun a => S.measurements.alice_pos _ _))
    (compressed_sum P hP.1 _ (hS.2.1 ⟨x.val,by omega⟩))
    (row_sharp S I hS h hm P hP x y) (row_sharp S I hS h hm P hP x z)

theorem row_square {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x y : Fin 3) : rowCell S I P x y*rowCell S I P x y=rowActive S I P x := by
  exact line_square _ false P hP.1
    (compressed_positive P hP.1 _ (fun a => S.measurements.alice_pos _ _))
    (compressed_sum P hP.1 _ (hS.2.1 ⟨x.val,by omega⟩)) (row_sharp S I hS h hm P hP x) y

theorem row_product {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x : Fin 3) : rowCell S I P x 0*(rowCell S I P x 1*rowCell S I P x 2)=rowActive S I P x := by
  have hh := line_product _ false P hP.1
    (compressed_positive P hP.1 (rowPOVM S I x) (fun a => S.measurements.alice_pos _ _))
    (compressed_sum P hP.1 _ (hS.2.1 ⟨x.val,by omega⟩)) (row_sharp S I hS h hm P hP x)
  simpa only [rowCell,rowActive,Bool.false_eq_true,ite_false,one_smul] using hh

def colCell {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) (x y : Fin 3) : Op :=
  signed (compressed Q (colPOVM S I y)) (cellClass (decide (y.val=2)) x)

def colActive {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) (y : Fin 3) : Op :=
  active (compressed Q (colPOVM S I y))

theorem col_sharp {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalB (normalOfPure S) h) (Q : Op) (hQ : SupportOf h Q)
    (x y : Fin 3) (t : Fin 4) :
    Projection (coarse (compressed Q (colPOVM S I y)) (cellClass (decide (y.val=2)) x) t) := by
  rw [coarse_compressed]
  have hm' : MarginalA (normalOfPure (PureTransfer.flipPure S)) h := hm
  have hh := coarse_analysis (PureTransfer.flipPure S) h hm' Q hQ
    (colPOVM S I y) (rowPOVM S I x)
    (fun b => S.measurements.bob_pos _ _) (fun a => S.measurements.alice_pos _ _)
    (hS.2.2 ⟨y.val,by omega⟩) (hS.2.1 ⟨x.val,by omega⟩)
    (cellClass (decide (y.val=2)) x) (cellClass false y) ?_ t
  · exact hh.2.2.1
  · intro b a hab
    have hz := hS.1 ⟨x.val,by omega⟩ ⟨y.val,by omega⟩ a b
      (cellClass_forbidden x y a b (Ne.symm hab))
    rw [normalOfPure_probability] at hz
    have hz' := (PureTransfer.flipPure_probability S (I.qA ⟨x.val,by omega⟩)
      (I.qB ⟨y.val,by omega⟩) (I.aA a) (I.aB b)).trans hz
    unfold PureStrategy.probability at hz'
    exact hz'

theorem col_commute {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalB (normalOfPure S) h) (Q : Op) (hQ : SupportOf h Q)
    (x z y : Fin 3) : colCell S I Q x y*colCell S I Q z y=colCell S I Q z y*colCell S I Q x y := by
  apply signed_commute _ _ _ Q hQ.1
    (compressed_positive Q hQ.1 _ (fun b => S.measurements.bob_pos _ _))
    (compressed_sum Q hQ.1 _ (hS.2.2 ⟨y.val,by omega⟩))
    (fun t => col_sharp S I hS h hm Q hQ x y t) (fun t => col_sharp S I hS h hm Q hQ z y t)

theorem col_square {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalB (normalOfPure S) h) (Q : Op) (hQ : SupportOf h Q)
    (x y : Fin 3) : colCell S I Q x y*colCell S I Q x y=colActive S I Q y := by
  exact line_square _ _ Q hQ.1
    (compressed_positive Q hQ.1 _ (fun b => S.measurements.bob_pos _ _))
    (compressed_sum Q hQ.1 _ (hS.2.2 ⟨y.val,by omega⟩)) (fun j t => col_sharp S I hS h hm Q hQ j y t) x

theorem col_product {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalB (normalOfPure S) h) (Q : Op) (hQ : SupportOf h Q)
    (y : Fin 3) : colCell S I Q 0 y*(colCell S I Q 1 y*colCell S I Q 2 y)=
      (if y.val=2 then (-1:ℂ) else 1) • colActive S I Q y := by
  have hh := line_product _ (decide (y.val=2)) Q hQ.1
    (compressed_positive Q hQ.1 (colPOVM S I y) (fun b => S.measurements.bob_pos _ _))
    (compressed_sum Q hQ.1 _ (hS.2.2 ⟨y.val,by omega⟩))
    (fun j t => col_sharp S I hS h hm Q hQ j y t)
  simpa only [colCell,colActive,decide_eq_true_eq] using hh

#print axioms col_sharp
#print axioms col_product
#print axioms row_commute
#print axioms row_square
#print axioms row_product
end Sigma2.MagicCells
