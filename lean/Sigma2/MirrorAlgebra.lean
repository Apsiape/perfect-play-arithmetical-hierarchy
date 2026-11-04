import Sigma2.FiniteSpectral
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.MirrorAlgebra
open Compiler TensorLifts PureSupport Preliminaries Coefficients

theorem left_support {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    left P S.vector=S.vector := by
  ext ⟨i,j⟩
  exact congrArg (fun v : H => v i) (columns_supported S h hm P hP j)

theorem right_support {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalB (normalOfPure S) h) (Q : Op) (hQ : SupportOf h Q) :
    right Q S.vector=S.vector := by
  have hh := left_support (PureTransfer.flipPure S) h hm Q hQ
  have he := congrArg swap hh
  simpa only [PureTransfer.flipPure,PureTransfer.swap_left,swap_swap] using he

theorem compressed_mirror (v : AB) (P Q E F : Op)
    (hP : left P v=v) (hQ : right Q v=v) (hm : left E v=right F v) :
    left (P*E*P) v=right (Q*F*Q) v := by
  have hL : left (P*E*P) v=left E v := by
    simp only [left_mul]
    change left P (left E (left P v))=left E v
    rw [hP,hm]
    have hc := congrArg (fun T : BipOp => T v) (commute P F)
    change left P (right F v)=right F (left P v) at hc
    rw [hc,hP]
  have hR : right (Q*F*Q) v=right F v := by
    simp only [right_mul]
    change right Q (right F (right Q v))=right F v
    rw [hQ,← hm]
    have hc := congrArg (fun T : BipOp => T v) (commute E Q)
    change left E (right Q v)=right Q (left E v) at hc
    rw [← hc,hQ]
  rw [hL,hR,hm]

theorem mirror_mul (v : AB) (A B C D : Op)
    (hA : left A v=right C v) (hB : left B v=right D v) :
    left (A*B) v=right (D*C) v := by
  simp only [left_mul,right_mul]
  change left A (left B v)=right D (right C v)
  rw [hB]
  have hc := congrArg (fun T : BipOp => T v) (commute A D)
  change left A (right D v)=right D (left A v) at hc
  rw [hc,hA]

theorem local_eq {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (A B : Op) (hA : A*P=A) (hB : B*P=B) (he : left A S.vector=left B S.vector) : A=B := by
  have hz := columns_zero_support S h hm P hP (A-B) (by
    intro j
    have hh := congrArg (fun v : AB => column v j) he
    rw [column_left,column_left] at hh
    change A (column S.vector j)-B (column S.vector j)=0
    exact sub_eq_zero.mpr hh)
  rw [sub_mul,hA,hB] at hz
  exact sub_eq_zero.mp hz

theorem mirror_commute {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (A B C D : Op) (hA : A*P=A) (hB : B*P=B)
    (hAC : left A S.vector=right C S.vector) (hBD : left B S.vector=right D S.vector)
    (hCD : C*D=D*C) : A*B=B*A := by
  apply local_eq S h hm P hP _ _
    (by rw [mul_assoc,hB]) (by rw [mul_assoc,hA])
  rw [mirror_mul S.vector A B C D hAC hBD,
    mirror_mul S.vector B A D C hBD hAC,hCD]

#print axioms mirror_commute
end Sigma2.MirrorAlgebra
