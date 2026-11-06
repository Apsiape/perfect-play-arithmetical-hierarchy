import Sigma2.CalibrationFrame

noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationTransport
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral
  MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits QubitUnits FourUnits
  BridgeMatrixUnits DiagonalIdentification MirrorUnits CoefficientOperator MatrixCentralizer
  CalibrationEvents CalibrationCoefficients CalibrationGeometry CalibrationFrame

theorem op_eq_zero_of_neg (A : Op) (hA : A= -A) : A=0 := by
  have hh : (2:ℂ) • A=0 := by
    calc
      _=A+A := by module
      _=0 := eq_neg_iff_add_eq_zero.mp hA
  calc
    A=(1/2:ℂ) • ((2:ℂ) • A) := by module
    _=0 := by rw [hh,op_smul_zero]

/-- The off-diagonal block of a self-adjoint sign unitary, with exactly the
half-weighted modular commutator from the written proof. -/
theorem transport_from_sign (h f m X : Op)
    (hf : Projection f) (hm : Projection m) (hfm : f*m=0) (hmf : m*f=0)
    (hX : star X=X) (hXX : X*X=f+m)
    (hXS : X*(f+m)=X) (hSX : (f+m)*X=X)
    (hanti : X*(f-m)= -((f-m)*X))
    (hcf : h*f=f*h) (hcm : h*m=m*h)
    (hcal : X*((f+(1/2:ℂ) • m)*h)=((f+(1/2:ℂ) • m)*h)*X) :
    let w := m*X*f
    star w*w=f ∧ w*star w=m ∧ h*w=(2:ℂ) • (w*h) := by
  have hDf : (f-m)*f=f := by rw [sub_mul,hf.2,hmf,sub_zero]
  have hfD : f*(f-m)=f := by rw [mul_sub,hf.2,hfm,sub_zero]
  have hDm : (f-m)*m= -m := by rw [sub_mul,hfm,hm.2,zero_sub]
  have hmD : m*(f-m)= -m := by rw [mul_sub,hmf,hm.2,zero_sub]
  have hzff : f*X*f=0 := by
    apply op_eq_zero_of_neg
    calc
      f*X*f=f*(X*(f-m))*f := by
        calc
          _=f*X*((f-m)*f) := by rw [hDf]
          _=_ := by noncomm_ring
      _=f*(-((f-m)*X))*f := by rw [hanti]
      _= -(f*X*f) := by
        rw [PauliExtraction.op_mul_neg,PauliExtraction.op_neg_mul]
        rw [← mul_assoc f (f-m) X,hfD]
  have hzmm : m*X*m=0 := by
    apply op_eq_zero_of_neg
    have hh := congrArg (fun A : Op => m*A*m) hanti
    have heL : m*(X*(f-m))*m= -(m*X*m) := by
      calc
        _=m*X*((f-m)*m) := by noncomm_ring
        _=m*X*(-m) := by rw [hDm]
        _=_ := by rw [PauliExtraction.op_mul_neg]
    have heR : m*(-((f-m)*X))*m=m*X*m := by
      rw [PauliExtraction.op_mul_neg,PauliExtraction.op_neg_mul,← mul_assoc m (f-m) X,hmD,
        PauliExtraction.op_neg_mul,PauliExtraction.op_neg_mul,neg_neg]
    rw [heL,heR] at hh
    exact hh.symm
  have hXf : X*f=m*X*f := by
    calc
      X*f=((f+m)*X)*f := by rw [hSX]
      _=f*X*f+m*X*f := by noncomm_ring
      _=m*X*f := by rw [hzff,zero_add]
  have hXm : X*m=f*X*m := by
    calc
      X*m=((f+m)*X)*m := by rw [hSX]
      _=f*X*m+m*X*m := by noncomm_ring
      _=f*X*m := by rw [hzmm,add_zero]
  have hstar : star (m*X*f)=f*X*m := by
    rw [star_mul,star_mul,hf.1,hm.1,hX]
    noncomm_ring
  have hwf : star (m*X*f)*(m*X*f)=f := by
    rw [hstar]
    calc
      _=f*X*(m*m)*X*f := by noncomm_ring
      _=f*X*(m*X*f) := by rw [hm.2]; noncomm_ring
      _=f*X*(X*f) := by rw [← hXf]
      _=f*(X*X)*f := by noncomm_ring
      _=f := by rw [hXX,mul_add,add_mul,hf.2,hfm,zero_mul,add_zero,hf.2]
  have hwm : (m*X*f)*star (m*X*f)=m := by
    rw [hstar]
    calc
      _=m*X*(f*f)*X*m := by noncomm_ring
      _=m*X*(f*X*m) := by rw [hf.2]; noncomm_ring
      _=m*X*(X*m) := by rw [← hXm]
      _=m*(X*X)*m := by noncomm_ring
      _=m := by rw [hXX,mul_add,add_mul,hmf,hm.2,zero_mul,zero_add,hm.2]
  have hKf : ((f+(1/2:ℂ) • m)*h)*f=f*h := by
    rw [mul_assoc,hcf,← mul_assoc,add_mul,smul_mul_assoc,hf.2,hmf,op_smul_zero,add_zero]
  have hmK : m*((f+(1/2:ℂ) • m)*h)=(1/2:ℂ) • (m*h) := by
    rw [← mul_assoc,mul_add,mul_smul_comm,hmf,hm.2,zero_add,smul_mul_assoc]
  have hblock : (m*X*f)*h=(1/2:ℂ) • (h*(m*X*f)) := by
    calc
      _=m*(X*((f+(1/2:ℂ) • m)*h))*f := by
        calc
          _=m*X*(((f+(1/2:ℂ) • m)*h)*f) := by rw [hKf]; noncomm_ring
          _=_ := by noncomm_ring
      _=m*((((f+(1/2:ℂ) • m)*h)*X))*f := by rw [hcal]
      _=(m*((f+(1/2:ℂ) • m)*h))*X*f := by noncomm_ring
      _=((1/2:ℂ) • (m*h))*X*f := by rw [hmK]
      _=(1/2:ℂ) • (h*(m*X*f)) := by rw [← hcm]; simp only [smul_mul_assoc]; congr 1 <;> noncomm_ring
  refine ⟨hwf,hwm,?_⟩
  calc
    h*(m*X*f)=(2:ℂ) • ((1/2:ℂ) • (h*(m*X*f))) := by module
    _=(2:ℂ) • ((m*X*f)*h) := by rw [← hblock]

#print axioms transport_from_sign
end Sigma2.CalibrationTransport
