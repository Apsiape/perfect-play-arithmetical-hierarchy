import Sigma2.MagicCells
import Sigma2.MirrorAlgebra
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.MagicRelations
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral MagicCells MirrorAlgebra

theorem right_sub (A B : Op) : right (A-B)=right A-right B := by
  ext v ⟨i,j⟩
  simp only [right_apply,sub_apply,lp.coeFn_sub,Pi.sub_apply]

theorem left_smul (c : ℂ) (A : Op) : left (c • A)=c • left A := by
  ext v ⟨i,j⟩
  simp only [left_apply,smul_apply,lp.coeFn_smul,Pi.smul_apply]

theorem right_smul (c : ℂ) (A : Op) : right (c • A)=c • right A := by
  ext v ⟨i,j⟩
  simp only [right_apply,smul_apply,lp.coeFn_smul,Pi.smul_apply]

theorem signed_supported {ι : Type} [Fintype ι] (P : Op) (hP : Projection P)
    (A : ι → Op) (p : ι → Fin 4) : signed (compressed P A) p*P=signed (compressed P A) p := by
  simp only [signed,coarse,compressed,sub_mul,Finset.sum_mul,ite_mul,zero_mul,mul_assoc,hP.2]

theorem active_supported (P : Op) (hP : Projection P) (A : Fin 6 → Op) :
    active (compressed P A)*P=active (compressed P A) := by
  simp only [active,compressed,add_mul,mul_assoc,hP.2]

theorem cells_mirror {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 3) :
    left (rowCell S I P x y) S.vector=right (colCell S I Q x y) S.vector := by
  have hp := left_support S hA hmA P hP
  have hq := right_support S hB hmB Q hQ
  have h1 := compressed_mirror S.vector P Q _ _ hp hq (conditional_cells S I hS hA hmA P hP x y 1).1
  have h2 := compressed_mirror S.vector P Q _ _ hp hq (conditional_cells S I hS hA hmA P hP x y 2).1
  simp only [rowCell,colCell,signed,coarse_compressed,left_sub,right_sub,sub_apply]
  exact congrArg₂ (fun v w : AB => v-w) h1 h2

theorem column_commute {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA : Density)
    (hmA : MarginalA (normalOfPure S) hA) (P : Op) (hP : SupportOf hA P) (x z y : Fin 3) :
    rowCell S I P x y*rowCell S I P z y=rowCell S I P z y*rowCell S I P x y := by
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  exact mirror_commute S hA hmA P hP _ _ _ _
    (signed_supported P hP.1 _ _) (signed_supported P hP.1 _ _)
    (cells_mirror S I hS hA hB hmA hmB P Q hP hQ x y)
    (cells_mirror S I hS hA hB hmA hmB P Q hP hQ z y)
    (col_commute S I hS hB hmB Q hQ x z y)

theorem active_mirror {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (x y : Fin 3) :
    left (rowActive S I P x) S.vector=right (colActive S I Q y) S.vector := by
  have hc := cells_mirror S I hS hA hB hmA hmB P Q hP hQ x y
  have hh := mirror_mul S.vector _ _ _ _ hc hc
  rwa [row_square S I hS hA hmA P hP x y,col_square S I hS hB hmB Q hQ x y] at hh

theorem common_active {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA : Density)
    (hmA : MarginalA (normalOfPure S) hA) (P : Op) (hP : SupportOf hA P) (x : Fin 3) :
    rowActive S I P x=rowActive S I P 0 := by
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  apply local_eq S hA hmA P hP _ _
    (active_supported P hP.1 _) (active_supported P hP.1 _)
  change left (rowActive S I P x) S.vector=left (rowActive S I P 0) S.vector
  rw [active_mirror S I hS hA hB hmA hmB P Q hP hQ x 0,
    active_mirror S I hS hA hB hmA hmB P Q hP hQ 0 0]

theorem column_product {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA : Density)
    (hmA : MarginalA (normalOfPure S) hA) (P : Op) (hP : SupportOf hA P) (y : Fin 3) :
    rowCell S I P 0 y*(rowCell S I P 1 y*rowCell S I P 2 y)=
      (if y.val=2 then (-1:ℂ) else 1) • rowActive S I P 0 := by
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  have hc := cells_mirror S I hS hA hB hmA hmB P Q hP hQ
  have hh12 := mirror_mul S.vector _ _ _ _ (hc 1 y) (hc 2 y)
  have hh := mirror_mul S.vector _ _ _ _ (hc 0 y) hh12
  have hr : (colCell S I Q 2 y*colCell S I Q 1 y)*colCell S I Q 0 y=
      colCell S I Q 0 y*(colCell S I Q 1 y*colCell S I Q 2 y) := by
    rw [col_commute S I hS hB hmB Q hQ 2 1 y,mul_assoc,
      col_commute S I hS hB hmB Q hQ 2 0 y,← mul_assoc,
      col_commute S I hS hB hmB Q hQ 1 0 y,mul_assoc]
  rw [hr,col_product S I hS hB hmB Q hQ y,right_smul] at hh
  apply local_eq S hA hmA P hP _ _
  · simp only [rowCell,mul_assoc,signed_supported P hP.1]
  · simp only [rowActive,smul_mul_assoc,active_supported P hP.1]
  · rw [left_smul]
    change _=(if y.val=2 then (-1:ℂ) else 1) • left (rowActive S I P 0) S.vector
    rw [active_mirror S I hS hA hB hmA hmB P Q hP hQ 0 y]
    exact hh

#print axioms column_commute
#print axioms common_active
#print axioms column_product
end Sigma2.MagicRelations
