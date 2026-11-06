import Sigma2.CompilerAlgebra
noncomputable section
open scoped BigOperators
namespace Sigma2.ProjectionGraph
open CompilerAlgebra Preliminaries

theorem op_neg_mul (A B : Op) : (-A)*B= -(A*B) := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

theorem op_mul_neg (A B : Op) : A*(-B)= -(A*B) := by
  apply ContinuousLinearMap.ext
  intro v
  exact map_neg A (B v)

theorem op_eq_zero_of_neg (A : Op) (hA : A= -A) : A=0 := by
  have hh : (2:ℂ) • A=0 := by
    calc
      _=A+A := by module
      _=0 := eq_neg_iff_add_eq_zero.mp hA
  calc
    A=(1/2:ℂ) • ((2:ℂ) • A) := by module
    _=0 := by rw [hh,op_smul_zero]

/-- The two corner identities of an off-diagonal supported reflection. -/
theorem off_diagonal (f m X : Op)
    (hf : Projection f) (hm : Projection m) (hfm : f*m=0) (hmf : m*f=0)
    (hX : star X=X) (hXX : X*X=f+m)
    (hXS : X*(f+m)=X) (hSX : (f+m)*X=X)
    (hanti : X*(f-m)= -((f-m)*X)) :
    star (m*X*f)*(m*X*f)=f ∧ (m*X*f)*star (m*X*f)=m := by
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
        rw [op_mul_neg,op_neg_mul,← mul_assoc f (f-m) X,hfD]
  have hzmm : m*X*m=0 := by
    apply op_eq_zero_of_neg
    have hh := congrArg (fun A : Op => m*A*m) hanti
    have heL : m*(X*(f-m))*m= -(m*X*m) := by
      calc
        _=m*X*((f-m)*m) := by noncomm_ring
        _=m*X*(-m) := by rw [hDm]
        _=_ := by rw [op_mul_neg]
    have heR : m*(-((f-m)*X))*m=m*X*m := by
      rw [op_mul_neg,op_neg_mul,← mul_assoc m (f-m) X,hmD,
        op_neg_mul,op_neg_mul,neg_neg]
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
  constructor
  · rw [hstar]
    calc
      _=f*X*(m*m)*X*f := by noncomm_ring
      _=f*X*(m*X*f) := by rw [hm.2]; noncomm_ring
      _=f*X*(X*f) := by rw [← hXf]
      _=f*(X*X)*f := by noncomm_ring
      _=f := by rw [hXX,mul_add,add_mul,hf.2,hfm,zero_mul,add_zero,hf.2]
  · rw [hstar]
    calc
      _=m*X*(f*f)*X*m := by noncomm_ring
      _=m*X*(f*X*m) := by rw [hf.2]; noncomm_ring
      _=m*X*(X*m) := by rw [← hXm]
      _=m*(X*X)*m := by noncomm_ring
      _=m := by rw [hXX,mul_add,add_mul,hmf,hm.2,zero_mul,zero_add,hm.2]

theorem graph_certificate (Fi Fj G H Gc Hc : Op)
    (hFi : Projection Fi) (hFj : Projection Fj) (horth : Fi*Fj=0)
    (hG : Projection G) (hH : Projection H) (hGc : Projection Gc) (hHc : Projection Hc)
    (sG : G+Gc=Fi+Fj) (sH : H+Hc=Fi+Fj)
    (hrow : (5:ℂ) • H+Fi+Fj=(3:ℂ) • Fi+(4:ℂ) • G) :
    let u := Fi*((2:ℂ) • G-(Fi+Fj))*Fj
    star u*u=Fj ∧ u*star u=Fi := by
  have hrev : Fj*Fi=0 := by
    have h := congrArg (fun A : Op => star A) horth
    simpa only [star_mul,hFi.1,hFj.1,show star (0:Op)=0 from star_zero Op] using h
  let S := Fi+Fj
  have hS : Projection S := by
    constructor
    · exact (star_add Fi Fj).trans (congrArg₂ (fun A B : Op => A+B) hFi.1 hFj.1)
    · dsimp [S]; rw [add_mul,mul_add,mul_add,hFi.2,hFj.2,horth,hrev]; abel
  have supports (A B : Op) (hA : Projection A) (hB : Projection B) (hs : A+B=S) :
      A*S=A ∧ S*A=A := by
    apply positive_below_projection A S
      (ContinuousLinearMap.IsPositive.of_isStarProjection ⟨hA.2,hA.1⟩) hS
    rw [← hs,add_sub_cancel_left]
    exact ContinuousLinearMap.IsPositive.of_isStarProjection ⟨hB.2,hB.1⟩
  have gs := supports G Gc hG hGc sG
  have hs := supports H Hc hH hHc sH
  let D := Fi-Fj
  let X := (2:ℂ) • G-S
  let Y := (2:ℂ) • H-S
  have reflection (A : Op) (hA : Projection A) (ha : A*S=A) (hb : S*A=A) :
      ((2:ℂ) • A-S)*((2:ℂ) • A-S)=S := by
    simp only [sub_mul,mul_sub,smul_mul_smul_comm,smul_mul_assoc,mul_smul_comm,
      hA.2,ha,hb,hS.2]
    module
  have hXX : X*X=S := reflection G hG gs.1 gs.2
  have hYY : Y*Y=S := reflection H hH hs.1 hs.2
  have hDD : D*D=S := by
    dsimp [D,S]
    rw [sub_mul,mul_sub,mul_sub,hFi.2,hFj.2,horth,hrev]
    abel
  have hR : (5:ℂ) • H+S=(3:ℂ) • Fi+(4:ℂ) • G := by
    calc
      _=(5:ℂ) • H+Fi+Fj := by dsimp [S]; abel
      _=_ := hrow
  have hlin : (3:ℂ) • D+(4:ℂ) • X=(5:ℂ) • Y := by
    calc
      _=(2:ℂ) • ((3:ℂ) • Fi+(4:ℂ) • G)-(7:ℂ) • S := by dsimp [D,X,S]; module
      _=(2:ℂ) • ((5:ℂ) • H+S)-(7:ℂ) • S := by rw [hR]
      _=_ := by dsimp [Y]; module
  have hsq : ((3:ℂ) • D+(4:ℂ) • X)*((3:ℂ) • D+(4:ℂ) • X)=(25:ℂ) • S := by
    rw [hlin,smul_mul_smul_comm,hYY]
    norm_num
  have hz : (12:ℂ) • (D*X+X*D)=0 := by
    calc
      _=((3:ℂ) • D+(4:ℂ) • X)*((3:ℂ) • D+(4:ℂ) • X)-
          (9:ℂ) • (D*D)-(16:ℂ) • (X*X) := by
        simp only [add_mul,mul_add,smul_mul_smul_comm]
        module
      _=0 := by rw [hsq,hDD,hXX]; module
  have hanti : X*D= -(D*X) := by
    have hh : D*X+X*D=0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
    exact eq_neg_of_add_eq_zero_right hh
  have hXS : X*S=X := by
    dsimp [X]
    rw [sub_mul,smul_mul_assoc,gs.1,hS.2]
  have hSX : S*X=X := by
    dsimp [X]
    rw [mul_sub,mul_smul_comm,gs.2,hS.2]
  have hX : star X=X := by
    dsimp [X]
    calc
      _=star ((2:ℂ) • G)-star S := star_sub ((2:ℂ) • G) S
      _=(2:ℂ) • G-S := by rw [star_smul,star_ofNat,hG.1,hS.1]
  exact off_diagonal Fj Fi X hFj hFi hrev horth hX
    (by simpa only [S,add_comm] using hXX)
    (by simpa only [S,add_comm] using hXS)
    (by simpa only [S,add_comm] using hSX)
    (by
      have hh := congrArg (fun A : Op => -A) hanti
      simpa only [D,sub_eq_add_neg,mul_add,add_mul,op_mul_neg,op_neg_mul,
        neg_add_rev,neg_neg] using hh)

#print axioms graph_certificate
end Sigma2.ProjectionGraph

