import Sigma2.Preliminaries
noncomputable section
open scoped BigOperators
namespace Sigma2.RefinementAlgebra
open Preliminaries TensorLifts

theorem left_add (A B : Op) : left (A+B)=left A+left B := by
  ext v ⟨i,j⟩
  simp only [left_apply,add_apply,lp.coeFn_add,Pi.add_apply]

theorem right_add (A B : Op) : right (A+B)=right A+right B := by
  ext v ⟨i,j⟩
  simp only [right_apply,add_apply,lp.coeFn_add,Pi.add_apply]

theorem left_sub (A B : Op) : left (A-B)=left A-left B := by
  ext v ⟨i,j⟩
  simp only [left_apply,sub_apply,lp.coeFn_sub,Pi.sub_apply]

/-- Two complete binary effects with the same unchanged opposite mirrors are
identical on a filtered support when that vector has the local cancellation rule. -/
theorem binary_unique (v : AB) (P Q : Op) (E E' F : Fin 2 → Op)
    (hvP : left P v=v) (hvQ : right Q v=v)
    (hsE : E 0+E 1=P) (hsE' : E' 0+E' 1=P) (hsF : F 0+F 1=Q)
    (he : ∀ a,E a*P=E a) (he' : ∀ a,E' a*P=E' a)
    (hz : ∀ a b : Fin 2,a≠b → (left (E a)*right (F b)) v=0)
    (hz' : ∀ a b : Fin 2,a≠b → (left (E' a)*right (F b)) v=0)
    (cancel : ∀ A : Op,left A v=0 → A*P=0) : ∀ a,E' a=E a := by
  have mirror (A : Fin 2 → Op) (hs : A 0+A 1=P)
      (hzero : ∀ a b : Fin 2,a≠b → (left (A a)*right (F b)) v=0) :
      ∀ a,left (A a) v=right (F a) v := by
    have heq : left (A 0) v=right (F 0) v := by
      have hL : left (A 0) v=left (A 0) (right (F 0) v) := by
        calc
          _=left (A 0) (right Q v) := by rw [hvQ]
          _=_ := by
            rw [← hsF,right_add,add_apply,map_add]
            rw [show left (A 0) (right (F 1) v)=0 from hzero 0 1 (by decide),add_zero]
      have hR : right (F 0) v=left (A 0) (right (F 0) v) := by
        calc
          _=left P (right (F 0) v) := by
            have hc := congrArg (fun T : BipOp => T v) (commute P (F 0))
            change left P (right (F 0) v)=right (F 0) (left P v) at hc
            rw [hc,hvP]
          _=_ := by
            rw [← hs,left_add,add_apply]
            rw [show left (A 1) (right (F 0) v)=0 from hzero 1 0 (by decide),add_zero]
      exact hL.trans hR.symm
    intro a
    fin_cases a
    · exact heq
    · have hsum : left (A 0) v+left (A 1) v=right (F 0) v+right (F 1) v := by
        rw [← add_apply,← add_apply,← left_add,← right_add,hs,hsF,hvP,hvQ]
      rw [heq] at hsum
      exact add_left_cancel hsum
  have h0 := mirror E hsE hz
  have h1 := mirror E' hsE' hz'
  intro a
  have hdiff : left (E' a-E a) v=0 := by
    rw [left_sub,sub_apply,h1 a,h0 a,sub_self]
  have h := cancel (E' a-E a) hdiff
  rw [sub_mul,he' a,he a] at h
  exact sub_eq_zero.mp h

/-- A fine measurement with a sharp binary label marginal commutes with that
label, also when its total is a proper state-support projection. -/
theorem fine_commutes {n : ℕ} (e p : Op) (he : Projection e) (hp : Projection p)
    (hep : e*p=p) (hpe : p*e=p) (Q : Fin n → Fin 2 → Op)
    (hQ : ∀ a z,Positive (Q a z))
    (htotal : (∑ a,∑ z,Q a z)=e) (hcol : (∑ a,Q a 1)=p) :
    ∀ a,(∑ z,Q a z)*p=p*(∑ z,Q a z) := by
  have hcol0 : (∑ a,Q a 0)=e-p := by
    have hh := htotal
    simp only [Fin.sum_univ_two,Finset.sum_add_distrib,hcol] at hh
    exact eq_sub_of_add_eq hh
  have hcomp : Projection (e-p) := by
    constructor
    · exact (star_sub e p).trans (congrArg₂ (fun A B : Op => A-B) he.1 hp.1)
    · rw [sub_mul,mul_sub,mul_sub,he.2,hep,hpe,hp.2]; abel
  have hcp : (e-p)*p=0 := by rw [sub_mul,hep,hp.2,sub_self]
  have hpc : p*(e-p)=0 := by rw [mul_sub,hpe,hp.2,sub_self]
  intro a
  have hs1 := positive_below_projection (Q a 1) p (hQ a 1) hp (by
    rw [← hcol]; exact positive_sum_erase (fun b => Q b 1) (fun b => hQ b 1) a)
  have hs0 := positive_below_projection (Q a 0) (e-p) (hQ a 0) hcomp (by
    rw [← hcol0]; exact positive_sum_erase (fun b => Q b 0) (fun b => hQ b 0) a)
  have hzR : Q a 0*p=0 := by
    calc
      _=(Q a 0*(e-p))*p := by rw [hs0.1]
      _=0 := by rw [mul_assoc,hcp,mul_zero]
  have hzL : p*Q a 0=0 := by
    calc
      _=p*((e-p)*Q a 0) := by rw [hs0.2]
      _=0 := by rw [← mul_assoc,hpc,zero_mul]
  simp only [Fin.sum_univ_two,add_mul,mul_add,hzR,hzL,hs1.1,hs1.2,zero_add]

#print axioms binary_unique
#print axioms fine_commutes
end Sigma2.RefinementAlgebra
