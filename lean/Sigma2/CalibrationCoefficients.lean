import Sigma2.MirrorUnits

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationCoefficients
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer

/-- One base vector supplies every diagonal magic component. This is the
coordinate-free form of sum_k u_k tensor u_k tensor omega_mag. -/
theorem common_magic_vector {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    left (rowActive S I P 0) S.vector=
      ∑ i : Fin 4,(left (actualUnit S I P i 0)*right (bobUnit S I Q i 0))
        (left (actualUnit S I P 0 0) S.vector) := by
  have hu := units_analysis S I hS hA hmA P hP
  have hm := units_mirror S I hS hA hB hmA hmB P Q hP hQ
  have he (i : Fin 4) :
      (left (actualUnit S I P i 0)*right (bobUnit S I Q i 0))
        (left (actualUnit S I P 0 0) S.vector)=left (actualUnit S I P i i) S.vector := by
    change left (actualUnit S I P i 0)
      (right (bobUnit S I Q i 0) (left (actualUnit S I P 0 0) S.vector))=_
    have hc := congrArg (fun T : BipOp => T S.vector)
      (commute (actualUnit S I P 0 0) (bobUnit S I Q i 0))
    change left (actualUnit S I P 0 0) (right (bobUnit S I Q i 0) S.vector)=
      right (bobUnit S I Q i 0) (left (actualUnit S I P 0 0) S.vector) at hc
    rw [← hc]
    change left (actualUnit S I P i 0*actualUnit S I P 0 0)
      (right (bobUnit S I Q i 0) S.vector)=_
    rw [hu.1 i 0 0 0,if_pos rfl,← (hm 0 i).1]
    change left (actualUnit S I P i 0*actualUnit S I P 0 i) S.vector=_
    rw [hu.1 i 0 0 i,if_pos rfl]
  simp_rw [he]
  rw [← sum_apply,← left_sum,hu.2.2.2.2]

/-- The actual coefficient blocks, with density products and dense ranges in
the original flag and selected magic corners. The maps may have kernels. -/
theorem density_blocks {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    let f := P*flagA (normalOfPure S) I*P
    let m := P*magicA (normalOfPure S) I 0*P
    let Tf := coefficient (left f S.vector)
    let Tm := coefficient (left m S.vector)
    (Tf*star Tf=f*h.op ∧ Tf.range.topologicalClosure=f.range) ∧
    (Tm*star Tm=m*h.op ∧ Tm.range.topologicalClosure=m.range) := by
  have hu := units_analysis S I hS h hm P hP
  have hflag := SharpEvents.conditional_flag_sharp S I hS h hm P hP
  have hfcomm : h.op*(P*flagA (normalOfPure S) I*P)=(P*flagA (normalOfPure S) I*P)*h.op :=
    (((support_centralizes h P hP).mul_right hflag.2.2).mul_right (support_centralizes h P hP)).eq
  have hmcomm : h.op*(P*magicA (normalOfPure S) I 0*P)=(P*magicA (normalOfPure S) I 0*P)*h.op := by
    rw [← hu.2.2.1 0]
    exact hu.2.2.2.1 0 0
  exact ⟨corner_coefficient S h hm P hP _ hflag.2.1
      (by simp only [mul_assoc,hP.1.2]) hfcomm,
    corner_coefficient S h hm P hP _ (SharpEvents.conditional_magic_sharp S I hS h hm P hP 0).2.1
      (by simp only [mul_assoc,hP.1.2]) hmcomm⟩

theorem bob_diagonal {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (hA hB : Density)
    (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (i : Fin 4) :
    bobUnit S I Q i i=Q*S.measurements.bob (I.qB 0) (I.aB ⟨i.val+1,by omega⟩)*Q := by
  have hu := units_analysis S I hS hA hmA P hP
  have hm := (units_mirror S I hS hA hB hmA hmB P Q hP hQ i i).1
  have hm' := compressed_mirror S.vector P Q _ _ (left_support S hA hmA P hP)
    (right_support S hB hmB Q hQ) (magic_mirror S I hS hA hmA P hP i)
  rw [hu.2.2.1 i] at hm
  exact right_local_eq S hB hmB Q hQ _ _ (bobUnit_supported S I Q hQ.1 i i)
    (by simp only [mul_assoc,hQ.1.2]) (hm.symm.trans hm')

#print axioms common_magic_vector
#print axioms density_blocks
#print axioms bob_diagonal
end Sigma2.CalibrationCoefficients
