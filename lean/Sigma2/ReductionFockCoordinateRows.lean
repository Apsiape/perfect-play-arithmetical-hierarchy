import Sigma2.ReductionFockOperators

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 300000
namespace Sigma2.ReductionFockModel
open Sigma2.Tree FockModel
variable (q : ℕ) [NeZero q]

def ux : Op := perm q (Equiv.prodCongr xPermutation (Equiv.refl (Fin q)))
def uy : Op := perm q (Equiv.prodCongr yPermutation (Equiv.refl (Fin q)))
def px : Op := proj q {u | xCoord u.1=0}
def py : Op := proj q {u | yCoord u.1=0}

@[simp] lemma ux_basis (w : Word) (i : Fin q) :
    ux q (hilbertBasis q (w,i))=hilbertBasis q (nextX w,i) := perm_basis q _ _
@[simp] lemma uy_basis (w : Word) (i : Fin q) :
    uy q (hilbertBasis q (w,i))=hilbertBasis q (nextY w,i) := perm_basis q _ _
@[simp] lemma px_basis (w : Word) (i : Fin q) :
    px q (hilbertBasis q (w,i))=if xCoord w=0 then hilbertBasis q (w,i) else 0 := by
  have h := proj_basis q {u | xCoord u.1=0} (w,i)
  by_cases hx : xCoord w=0 <;> simpa [px,hx] using h
@[simp] lemma py_basis (w : Word) (i : Fin q) :
    py q (hilbertBasis q (w,i))=if yCoord w=0 then hilbertBasis q (w,i) else 0 := by
  have h := proj_basis q {u | yCoord u.1=0} (w,i)
  by_cases hy : yCoord w=0 <;> simpa [py,hy] using h

lemma ux_unitary : Unitary (ux q) := perm_unitary q _
lemma uy_unitary : Unitary (uy q) := perm_unitary q _
lemma px_projection : Projection (px q) := proj_projection q _
lemma py_projection : Projection (py q) := proj_projection q _

lemma ux_centralizer : Centralizes (density q).op (ux q) := by
  apply perm_centralizer
  rintro ⟨w,i⟩
  exact (nextX_geometry w).1
lemma uy_centralizer : Centralizes (density q).op (uy q) := by
  apply perm_centralizer
  rintro ⟨w,i⟩
  exact (nextY_geometry w).1
lemma px_centralizer : Centralizes (density q).op (px q) := diag_centralizer q _ _
lemma py_centralizer : Centralizes (density q).op (py q) := diag_centralizer q _ _

lemma ux_root : ux q*root q=root q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  cases w <;> simp [mul_apply_eq_comp,root_basis,nextX]
lemma uy_root : uy q*root q=root q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  cases w <;> simp [mul_apply_eq_comp,root_basis,nextY]
lemma px_root : px q*root q=root q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  cases w <;> simp [mul_apply_eq_comp,root_basis,xCoord]
lemma py_root : py q*root q=root q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  cases w <;> simp [mul_apply_eq_comp,root_basis,yCoord]

lemma ux_rec (b : Fin 2) :
    ux q*creation q ⟨b.val,by omega⟩=creation q ⟨b.val+2,by omega⟩ ∧
    ux q*creation q ⟨b.val+2,by omega⟩=creation q ⟨b.val,by omega⟩*ux q := by
  constructor <;> apply ambient_ext q <;> rintro ⟨w,i⟩ <;>
    fin_cases b <;> simp [mul_apply_eq_comp,creation_basis,ux_basis,nextX]

lemma uy_rec (a : Fin 2) :
    uy q*creation q ⟨2*a.val,by omega⟩=creation q ⟨2*a.val+1,by omega⟩ ∧
    uy q*creation q ⟨2*a.val+1,by omega⟩=creation q ⟨2*a.val,by omega⟩*uy q := by
  constructor <;> apply ambient_ext q <;> rintro ⟨w,i⟩ <;>
    fin_cases a <;> simp [mul_apply_eq_comp,creation_basis,uy_basis,nextY]

lemma px_rec (b : Fin 2) :
    px q*creation q ⟨b.val,by omega⟩=creation q ⟨b.val,by omega⟩*px q ∧
    px q*creation q ⟨b.val+2,by omega⟩=0 := by
  constructor <;> apply ambient_ext q <;> rintro ⟨w,i⟩ <;>
    fin_cases b <;> by_cases hx : xCoord w=0 <;> simp [mul_apply_eq_comp,creation_basis,px_basis,xCoord,apply_ite,map_zero,hx]

lemma py_rec (a : Fin 2) :
    py q*creation q ⟨2*a.val,by omega⟩=creation q ⟨2*a.val,by omega⟩*py q ∧
    py q*creation q ⟨2*a.val+1,by omega⟩=0 := by
  constructor <;> apply ambient_ext q <;> rintro ⟨w,i⟩ <;>
    fin_cases a <;> by_cases hy : yCoord w=0 <;> simp [mul_apply_eq_comp,creation_basis,py_basis,yCoord,apply_ite,map_zero,hy]

lemma ux_uy : ux q*uy q=uy q*ux q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  simp only [mul_apply_eq_comp,ux_basis,uy_basis,nextX_nextY]

#print axioms ux_rec
#print axioms uy_rec
#print axioms px_rec
#print axioms py_rec
end Sigma2.ReductionFockModel
