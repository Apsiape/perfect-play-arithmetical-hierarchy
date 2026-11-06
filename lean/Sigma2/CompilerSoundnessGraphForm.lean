import Sigma2.CompilerSoundnessGraphs

/-! Full supported graph and triangle identities in the actual extracted frame. -/
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessGraphForm
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessFrame CompilerSoundnessGraphs Preliminaries ProjectionGraph
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

theorem offdiagonal_form (f m X : Op) (hf : Projection f) (hm : Projection m)
    (hfm : f*m=0) (hmf : m*f=0)
    (hXS : X*(f+m)=X) (hSX : (f+m)*X=X)
    (hanti : X*(f-m)= -((f-m)*X)) : X=f*X*m+m*X*f := by
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

  calc
    X=X*(f+m) := hXS.symm
    _=X*f+X*m := mul_add _ _ _
    _=f*X*m+m*X*f := by rw [hXf,hXm]; abel

theorem graph_form (Fi Fj G H Gc Hc : Op)
    (hFi : Projection Fi) (hFj : Projection Fj) (horth : Fi*Fj=0)
    (hG : Projection G) (hH : Projection H) (hGc : Projection Gc) (hHc : Projection Hc)
    (sG : G+Gc=Fi+Fj) (sH : H+Hc=Fi+Fj)
    (hrow : (5:ℂ) • H+Fi+Fj=(3:ℂ) • Fi+(4:ℂ) • G) :
    let u := Fi*((2:ℂ) • G-(Fi+Fj))*Fj
    (2:ℂ) • G=Fi+Fj+u+star u := by
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

  have hoff := offdiagonal_form Fi Fj X hFi hFj horth hrev hXS hSX hanti
  have hstar : star (Fi*X*Fj)=Fj*X*Fi := by
    rw [star_mul,star_mul,hFi.1,hFj.1,hX]
    noncomm_ring
  change (2:ℂ) • G=Fi+Fj+(Fi*X*Fj)+star (Fi*X*Fj)
  rw [hstar]
  calc
    _=Fi+Fj+X := by dsimp [X,S]; module
    _=_ := by simpa only [add_assoc] using congrArg (fun Z : Op => Fi+Fj+Z) hoff

theorem named_graph_form (P : Presentation) (e : Op) (F : ProjectionName → Op)
    (hp : ∀ n,Projection (F n))
    (hframe : ∀ i j : Fin 3,F (.frame i.val)*F (.frame j.val)=
      if i=j then F (.frame j.val) else 0)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0)
    (w : Word) (hw : w ∈ words P) (k : Fin 3) :
    (2:ℂ) • F (.graph w k.val 0)=
      F (.frame (pairs[k.val]?.getD (0,1)).1)+F (.frame (pairs[k.val]?.getD (0,1)).2)+
        graphBlock F w k.val+star (graphBlock F w k.val) := by
  obtain ⟨h0,h1,h2⟩ := graph_equations e F w k.val (fun r hr => hrows r (graphRow_mem P w hw k r hr))
  apply graph_form _ _ _ _ _ _ (hp _) (hp _) _ (hp _) (hp _) (hp _) (hp _) h0 h1 h2
  fin_cases k
  · simpa [pairs] using hframe 0 (1:Fin 3)
  · simpa [pairs] using hframe 0 (2:Fin 3)
  · simpa [pairs] using hframe 1 (2:Fin 3)

theorem triangle_sum (P : Presentation) (e : Op) (F : ProjectionName → Op)
    (hp : ∀ n,Projection (F n))
    (hframe : ∀ i j : Fin 3,F (.frame i.val)*F (.frame j.val)=
      if i=j then F (.frame j.val) else 0)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0)
    (u v w : Word) (hu : u ∈ words P) (hv : v ∈ words P) (hw : w ∈ words P)
    (htri : triangleRow u v w ∈ rowList P) :
    (3:ℂ) • F (.triangle u v w)=e+
      graphBlock F u 0+star (graphBlock F u 0)+
      graphBlock F v 2+star (graphBlock F v 2)+
      graphBlock F w 1+star (graphBlock F w 1) := by
  have hr : (3:ℂ) • F (.triangle u v w)=
      (2:ℂ) • F (.graph u 0 0)+(2:ℂ) • F (.graph v 2 0)+
      (2:ℂ) • F (.graph w 1 0)-e := by
    have hh := hrows (triangleRow u v w) htri
    apply sub_eq_zero.mp
    calc
      _=evalRow e F (triangleRow u v w) := by simp [evalRow,triangleRow,row]; module
      _=0 := hh
  have hf := frame_sum P e F hrows
  have hs : F (.frame 0)+F (.frame 1)+F (.frame 2)=e := by
    simpa [Fin.sum_univ_succ,add_assoc] using hf
  have h0 := named_graph_form P e F hp hframe hrows u hu 0
  have h1 := named_graph_form P e F hp hframe hrows w hw 1
  have h2 := named_graph_form P e F hp hframe hrows v hv 2
  simp [pairs] at h0 h1 h2
  rw [hr,h0,h1,h2]
  rw [← hs]
  module

#print axioms graph_form
#print axioms named_graph_form
#print axioms triangle_sum
end Sigma2.CompilerSoundnessGraphForm
