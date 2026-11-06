import Sigma2.RowScalarGlobal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Explicit Hilbert coordinates for a complete finite matrix-unit algebra.
The coordinate Hilbert space is the finite L2 sum of copies of the 00 corner,
i.e. the completed tensor product with the finite scalar factor. -/
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.MatrixSupportCoordinates

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def space (P : Op) : Submodule ℂ H := (P-1).ker

@[simp] theorem mem_space (P : Op) (v : H) : v ∈ space P ↔ P v=v := by
  simp [space,sub_apply,sub_eq_zero]

structure Units (P : Op) (t : ι → ι → Op) : Prop where
  product : ∀ i j k l,t i j*t k l=if j=k then t i l else 0
  adjoint : ∀ i j,star (t i j)=t j i
  total : (∑ i,t i i)=P

variable {P : Op} {t : ι → ι → Op}

namespace Units

theorem supported (h : Units P t) (i j : ι) : P*t i j=t i j ∧ t i j*P=t i j := by
  rw [← h.total]
  constructor
  · simp only [Finset.sum_mul,h.product]; simp
  · simp only [Finset.mul_sum,h.product]; simp

def forward (h : Units P t) (o : ι) : space P →ₗ[ℂ] PiLp 2 (fun _ : ι => space (t o o)) where
  toFun v := WithLp.toLp 2 (fun i => ⟨t o i v,by
    rw [mem_space]
    change (t o o*t o i) (v:H)=t o i v
    rw [h.product,if_pos rfl]⟩)
  map_add' v w := by ext i; simp
  map_smul' c v := by ext i; simp

def backward (h : Units P t) (o : ι) : PiLp 2 (fun _ : ι => space (t o o)) →ₗ[ℂ] space P where
  toFun v := ⟨∑ i,t i o (v i),by
    rw [mem_space,map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun A : Op => A (v i:H)) (h.supported i o).1⟩
  map_add' v w := by ext; simp [map_add,Finset.sum_add_distrib]
  map_smul' c v := by ext; simp [map_smul,Finset.smul_sum]

def coordinateEquiv (h : Units P t) (o : ι) :
    space P ≃ₗ[ℂ] PiLp 2 (fun _ : ι => space (t o o)) :=
    { h.forward o with
      invFun := h.backward o
      left_inv := by
        intro v
        apply Subtype.ext
        change (∑ i,t i o (t o i (v:H)))=(v:H)
        simp only [← mul_apply_eq_comp,h.product,ite_true]
        rw [← ContinuousLinearMap.sum_apply,h.total]
        exact (mem_space P v).mp v.property
      right_inv := by
        intro v
        ext i : 1
        apply Subtype.ext
        change t o i (∑ j,t j o (v j))=(v i:H)
        simp only [map_sum,← mul_apply_eq_comp,h.product]
        rw [Finset.sum_eq_single i]
        · rw [if_pos rfl]
          exact (mem_space _ (v i)).mp (v i).property
        · intro b hb hbi
          rw [if_neg (Ne.symm hbi)]
          rfl
        · intro hi
          exact False.elim (hi (Finset.mem_univ i)) }

def coordinates (h : Units P t) (o : ι) :
    space P ≃ₗᵢ[ℂ] PiLp 2 (fun _ : ι => space (t o o)) := by
  letI := PiLp.innerProductSpace (𝕜 := ℂ) (fun _ : ι => space (t o o))
  refine LinearEquiv.isometryOfInner (h.coordinateEquiv o) ?_
  intro v w
  change (∑ i,inner ℂ (t o i (v:H)) (t o i (w:H)))=inner ℂ (v:H) (w:H)
  simp only [← ContinuousLinearMap.adjoint_inner_right,← mul_apply_eq_comp,← ContinuousLinearMap.star_eq_adjoint,h.adjoint,h.product,ite_true]
  rw [← inner_sum,← ContinuousLinearMap.sum_apply,h.total,(mem_space P w).mp w.property]

@[simp] theorem coordinates_apply (h : Units P t) (o i : ι) (v : space P) :
    ((h.coordinates o v) i : H)=t o i v := rfl

@[simp] theorem coordinates_symm_apply (h : Units P t) (o : ι)
    (v : PiLp 2 (fun _ : ι => space (t o o))) :
    ((h.coordinates o).symm v : H)=∑ i,t i o (v i) := rfl

/-- The actual matrix units become the standard scalar matrix units. -/
theorem unit_coordinates (h : Units P t) (o i j k : ι) (v : H) :
    t o k (t i j v)=if k=i then t o j v else 0 := by
  change (t o k*t i j) (v:H)=_
  rw [h.product]
  split_ifs <;> rfl

/-- Every supported commutant operator acts by the same corner operator on
all scalar coordinates, with no assumption about the corner dimension. -/
theorem commutant_coordinates (h : Units P t) (o i : ι) (A : Op)
    (hc : ∀ i j,Commute A (t i j)) (v : space P) :
    t o i (A v)=A (t o i v) := by
  exact congrArg (fun B : Op => B (v:H)) (hc o i).eq.symm

#print axioms coordinates
#print axioms unit_coordinates
#print axioms commutant_coordinates
#print axioms mem_space
#print axioms supported
#print axioms coordinates_apply
#print axioms coordinates_symm_apply

end Units
end Sigma2.MatrixSupportCoordinates