import Sigma2.ReductionFockWeyl

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 300000
namespace Sigma2.ReductionFockModel
open Sigma2.Tree FockModel
variable (q : ℕ) [NeZero q] (M : Automaton)

def classicalPulse (q y : ℕ) : Bool := decide (q∣y)
def symbol (c : Symbol M) : Op :=
  proj q {u | run M (classicalPulse q) (yCoord u.1) (xCoord u.1)=c}

lemma symbol_projection (c : Symbol M) : Projection (symbol q M c) := proj_projection q _
lemma symbol_centralizer (c : Symbol M) : Centralizes (density q).op (symbol q M c) := diag_centralizer q _ _

@[simp] lemma symbol_basis (c : Symbol M) (w : Word) (i : Fin q) :
    symbol q M c (hilbertBasis q (w,i))=
      if run M (classicalPulse q) (yCoord w) (xCoord w)=c then hilbertBasis q (w,i) else 0 := by
  have h := proj_basis q {u | run M (classicalPulse q) (yCoord u.1) (xCoord u.1)=c} (w,i)
  by_cases hc : run M (classicalPulse q) (yCoord w) (xCoord w)=c <;> simpa [symbol,hc] using h

lemma symbol_partition : (∑ c : Symbol M,symbol q M c)=1 := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  simp only [ContinuousLinearMap.sum_apply,symbol_basis]
  change (∑ c : Symbol M, if run M (classicalPulse q) (yCoord w) (xCoord w)=c
    then hilbertBasis q (w,i) else 0)=hilbertBasis q (w,i)
  simp

lemma symbol_orthogonal (c d : Symbol M) (hcd : c≠d) : symbol q M c*symbol q M d=0 := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  by_cases hd : run M (classicalPulse q) (yCoord w) (xCoord w)=d
  · have hc : run M (classicalPulse q) (yCoord w) (xCoord w)≠c := fun hc => hcd (hc.symm.trans hd)
    simp only [mul_apply_eq_comp,symbol_basis,ite_eq_left hd,ite_eq_right hc,zero_apply]
  · simp only [mul_apply_eq_comp,symbol_basis,ite_eq_right hd,map_zero,zero_apply]

lemma symbol_no_halt (hn : ∀ t x,run M (classicalPulse q) t x≠2) : symbol q M 2=0 := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  simp [symbol_basis,hn]

lemma initial_start : symbol q M 0*px q*py q=px q*py q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  by_cases hx : xCoord w=0 <;> by_cases hy : yCoord w=0 <;>
    simp [mul_apply_eq_comp,px_basis,py_basis,symbol_basis,hx,hy,run]

lemma initial_blank : symbol q M 1*(1-px q)*py q=(1-px q)*py q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  by_cases hx : xCoord w=0 <;> by_cases hy : yCoord w=0 <;>
    simp [mul_apply_eq_comp,px_basis,py_basis,symbol_basis,hx,hy,run]

@[simp] lemma ux_star_basis (w : Word) (i : Fin q) :
    star (ux q) (hilbertBasis q (w,i))=hilbertBasis q (prevX w,i) := by
  change star (perm q _) _=_
  rw [perm_star,perm_basis]
  rfl
@[simp] lemma uy_star_basis (w : Word) (i : Fin q) :
    star (uy q) (hilbertBasis q (w,i))=hilbertBasis q (prevY w,i) := by
  change star (perm q _) _=_
  rw [perm_star,perm_basis]
  rfl

def lastX : Op := star (ux q)*px q*ux q
def lastY : Op := star (uy q)*py q*uy q

@[simp] lemma lastX_basis (w : Word) (i : Fin q) :
    lastX q (hilbertBasis q (w,i))=
      if xCoord w+1=2^w.length then hilbertBasis q (w,i) else 0 := by
  have hx : xCoord (nextX w)=0 ↔ xCoord w+1=2^w.length := by
    rw [(nextX_geometry w).2.1]
    by_cases h : xCoord w+1=2^w.length <;> simp [h]
  by_cases h : xCoord w+1=2^w.length <;>
    simp [lastX,mul_apply_eq_comp,ux_basis,px_basis,apply_ite,hx,h]

@[simp] lemma lastY_basis (w : Word) (i : Fin q) :
    lastY q (hilbertBasis q (w,i))=
      if yCoord w+1=2^w.length then hilbertBasis q (w,i) else 0 := by
  have hy : yCoord (nextY w)=0 ↔ yCoord w+1=2^w.length := by
    rw [(nextY_geometry w).2.2]
    by_cases h : yCoord w+1=2^w.length <;> simp [h]
  by_cases h : yCoord w+1=2^w.length <;>
    simp [lastY,mul_apply_eq_comp,uy_basis,py_basis,apply_ite,hy,h]

def leftFactor (l : Option (Symbol M)) : Op := match l with
  | none => px q
  | some c => ux q*symbol q M c*star (ux q)*(1-px q)
def rightFactor (r : Symbol M) : Op :=
  star (ux q)*symbol q M r*ux q*(1-lastX q)+(if r=1 then lastX q else 0)
def event (ε : Bool) : Op := if ε then pulse q else 1-pulse q

lemma left_basis (w : Word) (i : Fin q) (l : Option (Symbol M)) :
    leftFactor q M l (hilbertBasis q (w,i))=
      if (if xCoord w=0 then none else some (run M (classicalPulse q) (yCoord w) (xCoord w-1)))=l
        then hilbertBasis q (w,i) else 0 := by
  cases l with
  | none => by_cases hx : xCoord w=0 <;> simp [leftFactor,px_basis,hx]
  | some c =>
    by_cases hx : xCoord w=0 <;>
      by_cases hc : run M (classicalPulse q) (yCoord w) (xCoord w-1)=c <;>
      simp [leftFactor,mul_apply_eq_comp,px_basis,ux_star_basis,symbol_basis,ux_basis,
        hx,hc,apply_ite,prevX_geometry,nextX_prevX]

lemma right_basis (w : Word) (i : Fin q) (r : Symbol M) :
    rightFactor q M r (hilbertBasis q (w,i))=
      if run M (classicalPulse q) (yCoord w) (xCoord w+1)=r then hilbertBasis q (w,i) else 0 := by
  simp only [rightFactor,add_apply,mul_apply_eq_comp,sub_apply,one_apply_eq_self,lastX_basis]
  by_cases hx : xCoord w+1=2^w.length
  · have hr : run M (classicalPulse q) (yCoord w) (xCoord w+1)=1 :=
      run_blank M _ _ _ (by have hb := (coord_bounds w).2; omega)
    by_cases hr1 : r=1 <;> simp only [ite_eq_left hx,sub_self,map_zero,hr,hr1,
      ite_true,ite_false,zero_apply,lastX_basis,hx,zero_add,eq_comm] <;> simp_all
  · by_cases hc : run M (classicalPulse q) (yCoord w) (xCoord w+1)=r <;>
      by_cases hr1 : r=1 <;>
      simp only [ite_eq_right hx,sub_zero,ux_basis,symbol_basis,(nextX_geometry w).2.1,
        (nextX_geometry w).2.2,hx,ite_false,hc,ite_true,apply_ite,map_zero,ux_star_basis,
        prevX_nextX,hr1,zero_apply,lastX_basis,add_zero] <;> split_ifs <;> simp_all

lemma event_basis (w : Word) (i : Fin q) (ε : Bool) :
    event q ε (hilbertBasis q (w,i))=
      if classicalPulse q (yCoord w)=ε then hilbertBasis q (w,i) else 0 := by
  cases ε <;> by_cases h : q∣yCoord w <;>
    simp [event,pulse,proj_basis,classicalPulse,h]

lemma transition_row (a : Symbol M) :
    (star (uy q)*symbol q M a*uy q-
      ∑ l : Option (Symbol M), ∑ c : Symbol M, ∑ r : Symbol M, ∑ ε : Bool,
        if M.update l c r ε=a then leftFactor q M l*symbol q M c*rightFactor q M r*event q ε else 0)*
      (1-lastY q)=0 := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  by_cases hy : yCoord w+1=2^w.length
  · simp [mul_apply_eq_comp,lastY_basis,hy]
  · have hs := ordered_update_sum M (leftFactor q M) (symbol q M) (rightFactor q M) (event q)
      (hilbertBasis q (w,i))
      (if xCoord w=0 then none else some (run M (classicalPulse q) (yCoord w) (xCoord w-1)))
      (run M (classicalPulse q) (yCoord w) (xCoord w))
      (run M (classicalPulse q) (yCoord w) (xCoord w+1)) (classicalPulse q (yCoord w))
      (left_basis q M w i) (fun c => symbol_basis q M c w i)
      (right_basis q M w i) (event_basis q w i) a
    have ht : (star (uy q)*symbol q M a*uy q) (hilbertBasis q (w,i))=
        if run M (classicalPulse q) (yCoord w+1) (xCoord w)=a then hilbertBasis q (w,i) else 0 := by
      by_cases ha : run M (classicalPulse q) (yCoord w+1) (xCoord w)=a <;>
        simp [mul_apply_eq_comp,uy_basis,symbol_basis,uy_star_basis,apply_ite,nextY_geometry,hy,ha]
    have hm : (1-lastY q) (hilbertBasis q (w,i))=hilbertBasis q (w,i) := by
      simp only [sub_apply,one_apply_eq_self,lastY_basis,ite_eq_right hy,sub_zero]
    rw [mul_apply_eq_comp,hm,sub_apply,ht,hs,zero_apply]
    simp only [run]
    split_ifs <;> simp_all

#print axioms symbol_partition
#print axioms initial_start
#print axioms initial_blank
#print axioms transition_row
end Sigma2.ReductionFockModel
