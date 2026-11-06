import Sigma2.FiniteAncillaState

/-! Operator-valued ancillary matrices, including Bob's transposed coordinates. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.FiniteAncilla
open Coefficients FiniteSum TensorLifts
variable (d : ℕ) [NeZero d]

def matrixOp (M : Matrix (Fin d) (Fin d) Op) : Op := ∑ a,∑ b,
  ((FiniteSum.insert (coordinates d) a).toContinuousLinearMap.comp (M a b)).comp
    (project (coordinates d) b)

@[simp] theorem fiber_matrixOp (M : Matrix (Fin d) (Fin d) Op) (v : H) (a : Fin d) :
    fiber (coordinates d) (matrixOp d M v) a=∑ b,M a b (fiber (coordinates d) v b) := by
  change project (coordinates d) a ((∑ i,∑ j,
    ((FiniteSum.insert (coordinates d) i).toContinuousLinearMap.comp (M i j)).comp
      (project (coordinates d) j)) v)=_
  simp only [sum_apply,map_sum,ContinuousLinearMap.comp_apply,project_apply,
    LinearIsometry.coe_toContinuousLinearMap,fiber_insert]
  simp

@[simp] theorem matrixOp_zero : matrixOp d 0=0 := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  simp only [fiber_matrixOp,Matrix.zero_apply,zero_apply,Finset.sum_const_zero,fiber_zero]

@[simp] theorem matrixOp_one : matrixOp d 1=1 := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  rw [fiber_matrixOp,Finset.sum_eq_single a]
  · simp only [Matrix.one_apply_eq,one_apply_eq_self]
  · intro b hb hba
    rw [Matrix.one_apply_ne (Ne.symm hba)]
    rfl
  · simp

@[simp] theorem matrixOp_add (M N : Matrix (Fin d) (Fin d) Op) :
    matrixOp d (M+N)=matrixOp d M+matrixOp d N := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  simp only [fiber_matrixOp,Matrix.add_apply,add_apply,fiber_add,Finset.sum_add_distrib]

@[simp] theorem matrixOp_smul (c : ℂ) (M : Matrix (Fin d) (Fin d) Op) :
    matrixOp d (c • M)=c • matrixOp d M := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  simp only [fiber_matrixOp,Matrix.smul_apply,smul_apply,fiber_smul,Finset.smul_sum]

theorem matrixOp_sum {η : Type} (t : Finset η) (M : η → Matrix (Fin d) (Fin d) Op) :
    matrixOp d (∑ i ∈ t,M i)=∑ i ∈ t,matrixOp d (M i) := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  change _=project (coordinates d) a ((∑ i ∈ t,matrixOp d (M i)) v)
  simp only [fiber_matrixOp,Matrix.sum_apply,sum_apply,map_sum,project_apply]
  exact Finset.sum_comm

@[simp] theorem matrixOp_mul (M N : Matrix (Fin d) (Fin d) Op) :
    matrixOp d (M*N)=matrixOp d M*matrixOp d N := by
  ext v : 1
  apply ext_fiber (coordinates d)
  intro a
  simp only [mul_apply_eq_comp,fiber_matrixOp,Matrix.mul_apply,sum_apply,map_sum]
  exact Finset.sum_comm

@[simp] theorem matrixOp_star (M : Matrix (Fin d) (Fin d) Op) :
    matrixOp d (star M)=star (matrixOp d M) := by
  ext v : 1
  apply ext_inner_left ℂ
  intro w
  change inner ℂ w (matrixOp d (star M) v)=inner ℂ w ((matrixOp d M).adjoint v)
  rw [ContinuousLinearMap.adjoint_inner_right,inner_fibers (coordinates d),
    inner_fibers (coordinates d)]
  simp only [fiber_matrixOp,inner_sum,sum_inner,Matrix.star_apply,
    ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
  exact Finset.sum_comm

theorem matrixOp_projection (M : Matrix (Fin d) (Fin d) Op)
    (hstar : star M=M) (hmul : M*M=M) : Projection (matrixOp d M) := by
  constructor
  · rw [← matrixOp_star,hstar]
  · rw [← matrixOp_mul,hmul]

theorem matrixOp_positive (M : Matrix (Fin d) (Fin d) Op)
    (hstar : star M=M) (hmul : M*M=M) : Positive (matrixOp d M) := by
  have h := matrixOp_projection d M hstar hmul
  exact ContinuousLinearMap.IsPositive.of_isStarProjection ⟨h.2,h.1⟩

@[simp] theorem fiber_left_matrixOp (M : Matrix (Fin d) (Fin d) Op)
    (v : AB) (a b : Fin d) :
    fiber (bipCoordinates d) (left (matrixOp d M) v) (a,b)=
      ∑ c,left (M a c) (fiber (bipCoordinates d) v (c,b)) := by
  ext ⟨i,j⟩
  change left (matrixOp d M) v (coordinates d (a,i),coordinates d (b,j))=_
  rw [left_apply]
  have hh := congrArg (fun w : H => w i)
    (fiber_matrixOp d M (column v (coordinates d (b,j))) a)
  change matrixOp d M (column v (coordinates d (b,j))) (coordinates d (a,i))=_ at hh
  rw [hh]
  simp only [lp.coeFn_sum,Finset.sum_apply,left_apply,sum_apply]
  rfl

@[simp] theorem fiber_right_matrixOp (M : Matrix (Fin d) (Fin d) Op)
    (v : AB) (a b : Fin d) :
    fiber (bipCoordinates d) (right (matrixOp d M) v) (a,b)=
      ∑ c,right (M b c) (fiber (bipCoordinates d) v (a,c)) := by
  ext ⟨i,j⟩
  change right (matrixOp d M) v (coordinates d (a,i),coordinates d (b,j))=_
  rw [right_apply]
  have hh := congrArg (fun w : H => w j)
    (fiber_matrixOp d M (row v (coordinates d (a,i))) b)
  change matrixOp d M (row v (coordinates d (a,i))) (coordinates d (b,j))=_ at hh
  rw [hh]
  simp only [lp.coeFn_sum,Finset.sum_apply,right_apply,sum_apply]
  rfl

theorem left_matrix_entangle (M : Matrix (Fin d) (Fin d) Op) (v : AB) (a b : Fin d) :
    fiber (bipCoordinates d) (left (matrixOp d M) (entangle d v)) (a,b)=
      amplitude d • left (M a b) v := by
  rw [fiber_left_matrixOp]
  simp only [fiber_entangle]
  rw [Finset.sum_eq_single b]
  · simp only [ite_true,map_smul]
  · intro c hc hcb; simp only [if_neg hcb,map_zero]
  · simp

theorem right_matrix_entangle (M : Matrix (Fin d) (Fin d) Op) (v : AB) (a b : Fin d) :
    fiber (bipCoordinates d) (right (matrixOp d M) (entangle d v)) (a,b)=
      amplitude d • right (M b a) v := by
  rw [fiber_right_matrixOp]
  simp only [fiber_entangle]
  rw [Finset.sum_eq_single a]
  · simp only [ite_true,map_smul]
  · intro c hc hca; simp only [if_neg (Ne.symm hca),map_zero]
  · simp

/-- Bob's ancillary coordinates are transposed; old operator mirrors stay explicit. -/
theorem matrix_mirror (M N : Matrix (Fin d) (Fin d) Op) (v : AB)
    (hm : ∀ a b,left (M a b) v=right (N b a) v) :
    left (matrixOp d M) (entangle d v)=right (matrixOp d N) (entangle d v) := by
  apply ext_fiber (bipCoordinates d)
  intro ⟨a,b⟩
  rw [left_matrix_entangle,right_matrix_entangle,hm]

/-- Mirroring a noncommutative old product reverses its order on Bob's side. -/
theorem product_mirror (A B A' B' : Op) (v : AB)
    (hA : left A v=right A' v) (hB : left B v=right B' v) :
    left (A*B) v=right (B'*A') v := by
  rw [left_mul,right_mul]
  change left A (left B v)=right B' (right A' v)
  rw [hB]
  have hc := congrArg (fun L : BipOp => L v) (commute A B')
  change left A (right B' v)=right B' (left A v) at hc
  rw [hc,hA]

end Sigma2.FiniteAncilla
