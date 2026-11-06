import Sigma2.TableauGeometry

/-! Explicit inverse coordinate permutations on the finite word levels. -/
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 300000
namespace Sigma2.Tree

def prevX : Word → Word
  | [] => []
  | a::w => if h : a.val<2 then ⟨a.val+2,by omega⟩::prevX w
    else ⟨a.val-2,by omega⟩::w

def prevY : Word → Word
  | [] => []
  | a::w => if h : a.val%2=0 then ⟨a.val+1,by omega⟩::prevY w
    else ⟨a.val-1,by omega⟩::w

@[simp] lemma nextX_prevX (w : Word) : nextX (prevX w)=w := by
  induction w with
  | nil => rfl
  | cons a w ih => fin_cases a <;> simp [prevX,nextX,ih]

@[simp] lemma prevX_nextX (w : Word) : prevX (nextX w)=w := by
  induction w with
  | nil => rfl
  | cons a w ih => fin_cases a <;> simp [prevX,nextX,ih]

@[simp] lemma nextY_prevY (w : Word) : nextY (prevY w)=w := by
  induction w with
  | nil => rfl
  | cons a w ih => fin_cases a <;> simp [prevY,nextY,ih]

@[simp] lemma prevY_nextY (w : Word) : prevY (nextY w)=w := by
  induction w with
  | nil => rfl
  | cons a w ih => fin_cases a <;> simp [prevY,nextY,ih]

def xPermutation : Equiv.Perm Word :=
  ⟨nextX,prevX,prevX_nextX,nextX_prevX⟩
def yPermutation : Equiv.Perm Word :=
  ⟨nextY,prevY,prevY_nextY,nextY_prevY⟩

lemma nextX_nextY (w : Word) : nextX (nextY w)=nextY (nextX w) := by
  induction w with
  | nil => rfl
  | cons a w ih => fin_cases a <;> simp [nextX,nextY,ih]

lemma prevX_geometry (w : Word) :
    (prevX w).length=w.length ∧
    xCoord (prevX w)=(if xCoord w=0 then 2^w.length-1 else xCoord w-1) ∧
    yCoord (prevX w)=yCoord w := by
  have h := nextX_geometry (prevX w)
  rw [nextX_prevX] at h
  have hl := h.1.symm
  have hb := (coord_bounds (prevX w)).1
  rw [hl] at h hb
  refine ⟨hl,?_,h.2.2.symm⟩
  split_ifs at * <;> omega

lemma prevY_geometry (w : Word) :
    (prevY w).length=w.length ∧ xCoord (prevY w)=xCoord w ∧
    yCoord (prevY w)=(if yCoord w=0 then 2^w.length-1 else yCoord w-1) := by
  have h := nextY_geometry (prevY w)
  rw [nextY_prevY] at h
  have hl := h.1.symm
  have hb := (coord_bounds (prevY w)).2
  rw [hl] at h hb
  refine ⟨hl,h.2.1.symm,?_⟩
  split_ifs at * <;> omega

#print axioms xPermutation
#print axioms yPermutation
#print axioms nextX_nextY
end Sigma2.Tree
