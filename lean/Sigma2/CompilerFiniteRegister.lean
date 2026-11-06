import Sigma2.CompilerHonestLift
import Sigma2.RowCompletenessScalar

/-! Reusable diagonal and permutation operators on the common finite register.
The corner and axis allocations are the literal frozen numerical ones. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerFiniteRegister
open Compiler FiniteAncilla CompilerHonestDensity RowCompleteness
variable (d : ℕ) [NeZero d]

def diagonal (A : Fin d → Op) : Op := matrixOp d (Matrix.diagonal A)

@[simp] theorem diagonal_fiber (A : Fin d → Op) (v : H) (i : Fin d) :
    FiniteSum.fiber (coordinates d) (diagonal d A v) i=
      A i (FiniteSum.fiber (coordinates d) v i) := by
  rw [diagonal,fiber_matrixOp,Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Matrix.diagonal_apply,Ne.symm hji]
  · simp

@[simp] theorem diagonal_one : diagonal d (fun _ => 1)=1 := by
  rw [diagonal,show Matrix.diagonal (fun _ : Fin d => (1:Op))=1 from Matrix.diagonal_one,
    matrixOp_one]

@[simp] theorem diagonal_mul (A B : Fin d → Op) :
    diagonal d A*diagonal d B=diagonal d (fun i => A i*B i) := by
  rw [diagonal,diagonal,← matrixOp_mul,Matrix.diagonal_mul_diagonal]
  rfl

@[simp] theorem diagonal_star (A : Fin d → Op) :
    star (diagonal d A)=diagonal d (fun i => star (A i)) := by
  rw [diagonal,← matrixOp_star]
  congr 1
  ext i j
  by_cases hij : i=j
  · subst j; simp [Matrix.star_apply]
  · simp [Matrix.star_apply,Matrix.diagonal_apply,hij,Ne.symm hij,star_zero Op]

theorem diagonal_unitary (A : Fin d → Op) (hA : ∀ i,Unitary (A i)) :
    Unitary (diagonal d A) := by
  constructor
  · rw [diagonal_star,diagonal_mul]
    simpa only [(hA _).1] using diagonal_one d
  · rw [diagonal_star,diagonal_mul]
    simpa only [(hA _).2] using diagonal_one d

theorem diagonal_centralizer (w : Fin d → ℝ) (D : Op) (A : Fin d → Op)
    (hA : ∀ i,Centralizes D (A i)) :
    Centralizes (weightedOp d w D) (diagonal d A) := by
  have hw : diagonalBlocks d w D=Matrix.diagonal (fun i => (w i:ℂ) • D) := by
    ext i j
    by_cases hij : i=j <;> simp [diagonalBlocks,Matrix.diagonal_apply,hij]
  change matrixOp d (diagonalBlocks d w D)*diagonal d A=
    diagonal d A*matrixOp d (diagonalBlocks d w D)
  rw [hw]
  change diagonal d (fun i => (w i:ℂ) • D)*diagonal d A=
    diagonal d A*diagonal d (fun i => (w i:ℂ) • D)
  rw [diagonal_mul,diagonal_mul]
  congr 1
  funext i
  rw [smul_mul_assoc,mul_smul_comm,hA i]

def corner (a : Fin d) : Op := diagonal d (fun i => if i=a then 1 else 0)

theorem corner_projection (a : Fin d) : Projection (corner d a) := by
  constructor
  · rw [corner,diagonal_star]
    congr 1
    funext i
    split_ifs
    · exact star_one Op
    · exact star_zero Op
  · rw [corner,diagonal_mul]
    congr 1
    funext i
    split_ifs <;> simp

theorem corners_product (a b : Fin d) :
    corner d a*corner d b=if a=b then corner d a else 0 := by
  by_cases hab : a=b
  · subst b
    rw [if_pos rfl]
    exact (corner_projection d a).2
  · rw [if_neg hab,corner,corner,diagonal_mul]
    have h : (fun i : Fin d => (if i=a then (1:Op) else 0)*(if i=b then 1 else 0))=
        fun _ => (0:Op) := by
      funext i
      by_cases hi : i=a <;> by_cases hj : i=b <;> simp_all
    rw [h,diagonal]
    have hz : Matrix.diagonal (fun _ : Fin d => (0:Op))=0 := by ext i j; simp
    rw [hz,matrixOp_zero]

theorem corners_total : ∑ a : Fin d,corner d a=1 := by
  change (∑ a,matrixOp d ((diagonalPartition d).effect a))=1
  rw [← matrixOp_sum,(diagonalPartition d).total,matrixOp_one]

theorem corner_centralizer (w : Fin d → ℝ) (D : Op) (a : Fin d) :
    Centralizes (weightedOp d w D) (corner d a) := by
  apply diagonal_centralizer
  intro i
  split_ifs <;> simp [Centralizes]

/-- Each numbered copy fixes every other scalar corner. -/
def copy (a : Fin d) (U : Op) : Op := diagonal d (fun i => if i=a then U else 1)

theorem copy_unitary (a : Fin d) (U : Op) (hU : Unitary U) : Unitary (copy d a U) := by
  apply diagonal_unitary
  intro i
  split_ifs
  · exact hU
  · simp [Unitary]

theorem copy_centralizer (w : Fin d → ℝ) (D U : Op) (a : Fin d)
    (hU : Centralizes D U) : Centralizes (weightedOp d w D) (copy d a U) := by
  apply diagonal_centralizer
  intro i
  split_ifs
  · exact hU
  · simp [Centralizes]

/-- One block encoding repeats the same input unitary on any chosen active
corners; this is the operation needed for all four separate FMS refinements. -/
def repeated (active : Fin d → Bool) (U : Op) : Op :=
  diagonal d (fun i => if active i then U else 1)

theorem repeat_unitary (active : Fin d → Bool) (U : Op) (hU : Unitary U) :
    Unitary (repeated d active U) := by
  apply diagonal_unitary
  intro i
  split_ifs
  · exact hU
  · simp [Unitary]

theorem repeat_centralizer (w : Fin d → ℝ) (D U : Op) (active : Fin d → Bool)
    (hU : Centralizes D U) : Centralizes (weightedOp d w D) (repeated d active U) := by
  apply diagonal_centralizer
  intro i
  split_ifs
  · exact hU
  · simp [Centralizes]

/-- The actual four magic-corner indices for each frozen bridge. -/
def magicIndex (g : Fin 4) (k : Fin 4) : Fin 17 :=
  ⟨1+4*g.val+k.val,by have := g.isLt; have := k.isLt; omega⟩

def axisPerm (g : Fin 4) (k : Fin 2) : Equiv.Perm (Fin 17) :=
  if k=0 then
    Equiv.swap (magicIndex g 0) (magicIndex g 2)*Equiv.swap (magicIndex g 1) (magicIndex g 3)
  else
    Equiv.swap (magicIndex g 0) (magicIndex g 1)*Equiv.swap (magicIndex g 2) (magicIndex g 3)

theorem axisPerm_involutive (g : Fin 4) (k : Fin 2) :
    Function.Involutive (axisPerm g k) := by
  intro i
  fin_cases g <;> fin_cases k <;> fin_cases i <;>
    norm_num [axisPerm,magicIndex,Equiv.swap_apply_def,CompilerScaffold.cornerWeight ]

theorem axisPerm_weights (g : Fin 4) (k : Fin 2) (i : Fin 17) :
    CompilerScaffold.cornerWeight (axisPerm g k i)=CompilerScaffold.cornerWeight i := by
  fin_cases g <;> fin_cases k <;> fin_cases i <;>
    norm_num [axisPerm,magicIndex,Equiv.swap_apply_def,CompilerScaffold.cornerWeight ]

#print axioms copy_unitary
#print axioms repeat_centralizer
#print axioms corners_total
#print axioms axisPerm_involutive
#print axioms axisPerm_weights

/-- Every ancillary permutation is a genuine global unitary. -/
def permutation (e : Equiv.Perm (Fin d)) : Op := matrixOp d (permutationMatrix e)

theorem permutation_unitary (e : Equiv.Perm (Fin d)) : Unitary (permutation d e) := by
  have hl : permutationMatrix e.symm*permutationMatrix e=1 := by
    ext i j
    rw [permutation_left]
    simp [permutationMatrix,Matrix.one_apply,eq_comm]
  have hr : permutationMatrix e*permutationMatrix e.symm=1 := by
    ext i j
    rw [permutation_left]
    simp [permutationMatrix,Matrix.one_apply,eq_comm]
  constructor
  · rw [permutation,← matrixOp_star,permutation_star,← matrixOp_mul,hl,matrixOp_one]
  · rw [permutation,← matrixOp_star,permutation_star,← matrixOp_mul,hr,matrixOp_one]

theorem permutation_centralizer (w : Fin d → ℝ) (D : Op) (e : Equiv.Perm (Fin d))
    (hw : ∀ i,w (e i)=w i) :
    Centralizes (weightedOp d w D) (permutation d e) := by
  have hd : diagonalBlocks d w D=Matrix.diagonal (fun i => (w i:ℂ) • D) := by
    ext i j
    by_cases hij : i=j <;> simp [diagonalBlocks,Matrix.diagonal_apply,hij]
  change matrixOp d (diagonalBlocks d w D)*matrixOp d (permutationMatrix e)=
    matrixOp d (permutationMatrix e)*matrixOp d (diagonalBlocks d w D)
  rw [← matrixOp_mul,← matrixOp_mul,hd]
  congr 1
  ext i j
  rw [Matrix.diagonal_mul,permutation_left]
  by_cases hj : j=e i
  · subst j
    simp [permutationMatrix,hw]
  · simp [permutationMatrix,Matrix.diagonal_apply,hj,Ne.symm hj]

def axisUnitary (g : Fin 4) (k : Fin 2) : Op := permutation 17 (axisPerm g k)

theorem axisUnitary_unitary (g : Fin 4) (k : Fin 2) : Unitary (axisUnitary g k) :=
  permutation_unitary 17 _

theorem axisUnitary_selfadjoint (g : Fin 4) (k : Fin 2) :
    star (axisUnitary g k)=axisUnitary g k := by
  have he : (axisPerm g k).symm=axisPerm g k := by
    apply Equiv.ext
    intro i
    apply (axisPerm g k).injective
    simp only [Equiv.apply_symm_apply]
    exact (axisPerm_involutive g k i).symm
  change star (matrixOp 17 (permutationMatrix (axisPerm g k)))=_
  rw [← matrixOp_star,permutation_star,he]
  rfl

theorem axisUnitary_centralizer (h : Density) (g : Fin 4) (k : Fin 2) :
    Centralizes (scaffoldDensity h).op (axisUnitary g k) := by
  apply permutation_centralizer
  intro i
  exact_mod_cast axisPerm_weights g k i

def mask (active : Fin d → Bool) : Op := diagonal d (fun i => if active i then 1 else 0)

theorem mask_projection (active : Fin d → Bool) : Projection (mask d active) := by
  constructor
  · rw [mask,diagonal_star]
    congr 1
    funext i
    split_ifs
    · exact star_one Op
    · exact star_zero Op
  · rw [mask,diagonal_mul]
    congr 1
    funext i
    split_ifs <;> simp

def magicActive (g : Fin 4) (i : Fin 17) : Bool :=
  decide (((1 + 4 * g.val : ℕ) ≤ i.val) ∧ (i.val < (5 + 4 * g.val : ℕ)))

theorem magicActive_axis (g : Fin 4) (k : Fin 2) (i : Fin 17) :
    magicActive g (axisPerm g k i)=magicActive g i := by
  fin_cases g <;> fin_cases k <;> fin_cases i <;>
    norm_num [axisPerm,magicIndex,Equiv.swap_apply_def,CompilerScaffold.cornerWeight,magicActive]

theorem mask_permutation_commute (active : Fin d → Bool) (e : Equiv.Perm (Fin d))
    (ha : ∀ i,active (e i)=active i) :
    mask d active*permutation d e=permutation d e*mask d active := by
  rw [mask,diagonal,permutation,← matrixOp_mul,← matrixOp_mul]
  congr 1
  ext i j
  rw [Matrix.diagonal_mul,permutation_left]
  by_cases hj : j=e i
  · subst j
    simp [permutationMatrix,ha]
  · simp [permutationMatrix,Matrix.diagonal_apply,hj,Ne.symm hj]

def positiveAxis (g : Fin 4) (k : Fin 2) : Op :=
  mask 17 (magicActive g)*((1/2:ℂ) • (1+axisUnitary g k))

theorem spectral_projection (X : Op) (hs : star X=X) (hX : Unitary X) :
    Projection ((1/2:ℂ) • (1+X)) := by
  have hsq : X*X=1 := by simpa only [hs] using hX.1
  constructor
  · rw [star_smul (1/2:ℂ) (1+X),star_add (1:Op) X,star_one,hs]
    norm_num
  · simp only [smul_mul_smul_comm,add_mul,mul_add,one_mul,mul_one,hsq]
    norm_num
    module

theorem positiveAxis_projection (g : Fin 4) (k : Fin 2) : Projection (positiveAxis g k) := by
  apply projection_product _ _ (mask_projection 17 _) (spectral_projection _
    (axisUnitary_selfadjoint g k) (axisUnitary_unitary g k))
  have hc := mask_permutation_commute 17 (magicActive g) (axisPerm g k) (magicActive_axis g k)
  change mask 17 _*((1/2:ℂ) • (1+axisUnitary g k))=
    ((1/2:ℂ) • (1+axisUnitary g k))*mask 17 _
  rw [mul_smul_comm,smul_mul_assoc,mul_add,add_mul,mul_one,one_mul]
  exact congrArg (fun A : Op => (1/2:ℂ) • (mask 17 (magicActive g)+A)) hc

#print axioms axisUnitary_unitary
#print axioms axisUnitary_centralizer
#print axioms positiveAxis_projection

end Sigma2.CompilerFiniteRegister
