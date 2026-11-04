import Sigma2.CalibrationEvents
import Sigma2.CoefficientSupport

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.MirrorUnits
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification

/-- Keep the adjoint equation as well as the mirror equation when forming words. -/
def AdjointMirror (v : AB) (A B : Op) : Prop :=
  left A v=right B v ∧ left (star A) v=right (star B) v

theorem adjointMirror_self (v : AB) (A B : Op)
    (hA : star A=A) (hB : star B=B) (hm : left A v=right B v) :
    AdjointMirror v A B := ⟨hm,by rw [hA,hB]; exact hm⟩

theorem adjointMirror_add (v : AB) (A B C D : Op)
    (h : AdjointMirror v A C) (k : AdjointMirror v B D) :
    AdjointMirror v (A+B) (C+D) := by
  constructor
  · simp only [left_add,right_add,add_apply,h.1,k.1]
  · change left (star (A+B)) v=right (star (C+D)) v
    rw [op_star_add,op_star_add,left_add,right_add]
    change left (star A) v+left (star B) v=right (star C) v+right (star D) v
    rw [h.2,k.2]

theorem adjointMirror_smul (v : AB) (A B : Op) (c : ℂ)
    (h : AdjointMirror v A B) : AdjointMirror v (c • A) (c • B) := by
  constructor
  · simp only [left_smul,right_smul,smul_apply,h.1]
  · simp only [star_smul,left_smul,right_smul,smul_apply,h.2]

theorem adjointMirror_mul (v : AB) (A B C D : Op)
    (h : AdjointMirror v A C) (k : AdjointMirror v B D) :
    AdjointMirror v (A*B) (D*C) := by
  exact ⟨mirror_mul v A B C D h.1 k.1,by
    rw [star_mul,star_mul]
    exact mirror_mul v _ _ _ _ k.2 h.2⟩

theorem adjointMirror_projector (v : AB) (e f Z W : Op)
    (he : AdjointMirror v e f) (hz : AdjointMirror v Z W) (b : Fin 2) :
    AdjointMirror v (projector e Z b) (projector f W b) :=
  adjointMirror_smul v _ _ _ (adjointMirror_add v _ _ _ _ he
    (adjointMirror_smul v _ _ _ hz))

def oppositeQubit (e X Z : Op) (a b : Fin 2) : Op :=
  if a=b then projector e Z b else projector e Z b*X

theorem adjointMirror_qubit (v : AB) (e f X Y Z W : Op)
    (he : AdjointMirror v e f) (hx : AdjointMirror v X Y)
    (hz : AdjointMirror v Z W) (a b : Fin 2) :
    AdjointMirror v (qubitUnit e X Z a b) (oppositeQubit f Y W a b) := by
  unfold qubitUnit oppositeQubit
  split_ifs
  · exact adjointMirror_projector v e f Z W he hz b
  · exact adjointMirror_mul v _ _ _ _ hx (adjointMirror_projector v e f Z W he hz b)

/-- The Bob system is the reversed word system in the original Bob-only cells. -/
def bobUnit {s} (S : PureStrategy s) (I : FMSInstance s) (Q : Op) (i j : Fin 4) : Op :=
  oppositeQubit (colActive S I Q 0) (colCell S I Q 0 1) (colCell S I Q 1 0)
    (index j).2 (index i).2 *
  oppositeQubit (colActive S I Q 0) (colCell S I Q 1 1) (colCell S I Q 0 0)
    (index j).1 (index i).1

theorem units_mirror {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (i j : Fin 4) :
    AdjointMirror S.vector (actualUnit S I P i j) (bobUnit S I Q j i) := by
  have hc (x y : Fin 3) : AdjointMirror S.vector (rowCell S I P x y) (colCell S I Q x y) :=
    adjointMirror_self _ _ _
      (signed_selfadjoint _ _ (row_sharp S I hS hA hmA P hP x y))
      (signed_selfadjoint _ _ (col_sharp S I hS hB hmB Q hQ x y))
      (cells_mirror S I hS hA hB hmA hmB P Q hP hQ x y)
  have he : AdjointMirror S.vector (rowActive S I P 0) (colActive S I Q 0) := by
    have hh := adjointMirror_mul _ _ _ _ _ (hc 0 0) (hc 0 0)
    rwa [row_square S I hS hA hmA P hP 0 0,col_square S I hS hB hmB Q hQ 0 0] at hh
  exact adjointMirror_mul _ _ _ _ _
    (adjointMirror_qubit _ _ _ _ _ _ _ he (hc 1 1) (hc 0 0) (index i).1 (index j).1)
    (adjointMirror_qubit _ _ _ _ _ _ _ he (hc 0 1) (hc 1 0) (index i).2 (index j).2)

theorem projector_supported (P e Z : Op) (he : e*P=e) (hz : Z*P=Z) (b : Fin 2) :
    projector e Z b*P=projector e Z b := by
  simp only [PauliMatrixUnits.projector,smul_mul_assoc,add_mul,he,hz]

theorem opposite_supported (P e X Z : Op) (he : e*P=e) (hx : X*P=X)
    (hz : Z*P=Z) (a b : Fin 2) : oppositeQubit e X Z a b*P=oppositeQubit e X Z a b := by
  unfold oppositeQubit
  split_ifs
  · exact projector_supported P e Z he hz b
  · rw [mul_assoc,hx]

theorem bobUnit_supported {s} (S : PureStrategy s) (I : FMSInstance s)
    (Q : Op) (hQ : Projection Q) (i j : Fin 4) : bobUnit S I Q i j*Q=bobUnit S I Q i j := by
  unfold bobUnit
  rw [mul_assoc]
  have hh := opposite_supported Q (colActive S I Q 0) (colCell S I Q 1 1) (colCell S I Q 0 0)
    (active_supported Q hQ _) (signed_supported Q hQ _ _) (signed_supported Q hQ _ _)
    (index j).1 (index i).1
  rw [hh]

theorem right_local_eq {s} (S : PureStrategy s) (hB : Density)
    (hmB : MarginalB (normalOfPure S) hB) (Q : Op) (hQ : SupportOf hB Q)
    (A B : Op) (hA : A*Q=A) (hB : B*Q=B) (he : right A S.vector=right B S.vector) : A=B := by
  apply local_eq (PureTransfer.flipPure S) _ hmB Q hQ A B hA hB
  have hh := congrArg swap he
  simpa only [PureTransfer.swap_right,PureTransfer.flipPure] using hh

/-- All Bob matrix-unit equations follow on his original support, using both
adjoint mirrors. No independent choice of phases or permutation is made. -/
theorem bob_units_analysis {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    (∀ i j k l,bobUnit S I Q i j*bobUnit S I Q k l=if j=k then bobUnit S I Q i l else 0) ∧
    (∀ i j,star (bobUnit S I Q i j)=bobUnit S I Q j i) := by
  have hu := units_analysis S I hS hA hmA P hP
  have hm := units_mirror S I hS hA hB hmA hmB P Q hP hQ
  have hs := bobUnit_supported S I Q hQ.1
  have hstar (i j : Fin 4) : star (bobUnit S I Q i j)=bobUnit S I Q j i := by
    -- First show left support of the adjoint via the mirrored, supported vector;
    -- uniqueness uses the original Bob support after compressing the adjoint.
    have hvec : right (star (bobUnit S I Q i j)) S.vector=right (bobUnit S I Q j i) S.vector := by
      rw [← (hm j i).2,hu.2.1 j i,(hm i j).1]
    have hQleft : Q*bobUnit S I Q i j=bobUnit S I Q i j := by
      -- Use cancellation of the part outside Q directly, without positivity.
      have hz : right ((1-Q)*bobUnit S I Q i j) S.vector=0 := by
        rw [right_mul]
        change right (1-Q) (right (bobUnit S I Q i j) S.vector)=0
        rw [← (hm j i).1]
        have hc := congrArg (fun T : BipOp => T S.vector) (commute (actualUnit S I P j i) (1-Q))
        change left (actualUnit S I P j i) (right (1-Q) S.vector)=
          right (1-Q) (left (actualUnit S I P j i) S.vector) at hc
        rw [← hc]
        have hzero : right (1-Q) S.vector=0 := by
          rw [right_sub,right_one,sub_apply,right_support S hB hmB Q hQ,one_apply_eq_self,sub_self]
        rw [hzero,map_zero]
      have heq := right_local_eq S hB hmB Q hQ ((1-Q)*bobUnit S I Q i j) 0
        (by rw [mul_assoc,hs]) (by simp) (by simpa only [right_zero,zero_apply] using hz)
      rw [sub_mul,one_mul] at heq
      exact (sub_eq_zero.mp heq).symm
    apply right_local_eq S hB hmB Q hQ _ _ _ (hs j i) hvec
    have hh := congrArg star hQleft
    simpa only [star_mul,hQ.1.1] using hh
  refine ⟨?_,hstar⟩
  intro i j k l
  apply right_local_eq S hB hmB Q hQ _ _ (by rw [mul_assoc,hs]) (by split_ifs <;> simp only [hs,zero_mul])
  have hh := mirror_mul S.vector _ _ _ _ (hm l k).1 (hm j i).1
  rw [hu.1 l k j i] at hh
  by_cases hjk : j=k
  · simp only [hjk,ite_true] at hh ⊢
    exact hh.symm.trans (hm l i).1
  · have hkj : k≠j := Ne.symm hjk
    simpa only [hkj,hjk,ite_false,left_zero,right_zero,map_zero] using hh.symm

#print axioms units_mirror
#print axioms bob_units_analysis
end Sigma2.MirrorUnits
