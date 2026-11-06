import Sigma2.CompilerHonestScalar

/-! All four scalar FMS families on the common honest infinite-dimensional
state, before and after the common qutrit factor. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerHonestFMSLift
open FiniteAncilla CompilerHonestDensity CompilerFiniteRegister
  CompilerHonestState CompilerHonestScalar CompilerHonestFMSWeights
  CoefficientOperator

/-- The actual common density of the pregame, including the qutrit. -/
def density (h : Density) : Density :=
  weightedDensity 3 (fun _ => (1/3:ℝ)) (fun _ => by norm_num)
    (by norm_num [Fin.sum_univ_three]) (scaffoldDensity h)

theorem weight_sqrt (i : Fin 17) :
    Real.sqrt (CompilerScaffold.cornerWeight i:ℝ)=
      (Real.sqrt 2)^((i.val+3)/4)/11 := by
  apply (Real.sqrt_eq_iff_eq_sq (by exact_mod_cast (CompilerScaffold.cornerWeight_positive i).le)
    (by positivity)).mpr
  have hp : ((Real.sqrt 2)^((i.val+3)/4))^2=(2:ℝ)^((i.val+3)/4) := by
    rw [← pow_mul,Nat.mul_comm ((i.val+3)/4) 2,pow_mul,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  norm_num [CompilerScaffold.cornerWeight,div_pow,hp]

theorem scaffold_root (h : Density) :
    root (scaffoldDensity h)=matrixOp 17 (blocks 17 CompilerHonestFMSWeights.coefficient (root h)) := by
  rw [scaffoldDensity,weighted_root]
  unfold weightedOp
  congr 1
  apply Matrix.ext
  intro i j
  by_cases hij : i=j
  · subst j
    simp only [diagonalBlocks,ite_true,blocks,CompilerHonestFMSWeights.coefficient,Matrix.diagonal_apply_eq]
    congr 1
    rw [weight_sqrt]
    push_cast
    rfl
  · simp only [diagonalBlocks,if_neg hij,blocks,CompilerHonestFMSWeights.coefficient,Matrix.diagonal_apply_ne _ hij]
    ext v i
    simp

/-- The finite matrix certificate annihilates an actual bipartite event on the
same purification for every bridge and both FMS question orientations. -/
theorem scaffold_rejection (h : Density) (g : Fin 4) (x y : Fin 5) (a b : Fin 6)
    (hr : Compiler.conditionalFmsRule x.val y.val a.val b.val=false) :
    scalarOp 17 ((CompilerHonestFamilies.alice g x).effect a)*root (scaffoldDensity h)*
      transpose (scalarOp 17 ((CompilerHonestFamilies.bob g y).effect b))=0 := by
  rw [scaffold_root,scalar_sandwich,CompilerHonestFMSWeights.rejection g x y a b hr]
  have hz : blocks 17 0 (root h)=0 := by ext i j; simp [blocks]
  rw [hz,matrixOp_zero]

@[simp] theorem amplify_zero_eq (d : ℕ) [NeZero d] : amplify d (0:Op)=0 := by
  ext v : 1
  apply FiniteSum.ext_fiber (coordinates d)
  intro a
  simp only [fiber_amplify,zero_apply,FiniteSum.fiber_zero]

def amplifyPartition {d : ℕ} [NeZero d] {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : RowCompleteness.Partition Op ι) : RowCompleteness.Partition Op ι where
  effect a := amplify d (P.effect a)
  selfadjoint a := by rw [← amplify_star,P.selfadjoint]
  product a b := by
    rw [← amplify_mul,P.product]
    split_ifs <;> simp
  total := by rw [← amplify_sum,P.total,amplify_one]

def alice (g : Fin 4) (x : Fin 5) : RowCompleteness.Partition Op (Fin 6) :=
  amplifyPartition (d:=3) (scalarPartition 17 (CompilerHonestFamilies.alice g x))

def bob (g : Fin 4) (x : Fin 5) : RowCompleteness.Partition Op (Fin 6) :=
  amplifyPartition (d:=3) (scalarPartition 17 (CompilerHonestFamilies.bob g x))

theorem transpose_amplify (d : ℕ) [NeZero d] (A : Op) :
    transpose (amplify d A)=amplify d (transpose A) := by
  rw [← RowCompleteness.matrixOp_constantDiagonal,transpose_matrix,
    ← RowCompleteness.matrixOp_constantDiagonal]
  congr 1
  ext i j
  by_cases hij : i=j
  · subst j; simp [RowCompleteness.constantDiagonal]
  · simp [RowCompleteness.constantDiagonal,Matrix.diagonal_apply,hij,Ne.symm hij]

theorem density_root (h : Density) :
    root (density h)=(Real.sqrt (1/3:ℝ):ℂ) • amplify 3 (root (scaffoldDensity h)) := by
  rw [density,weighted_root]
  ext v : 1
  apply FiniteSum.ext_fiber (coordinates 3)
  intro a
  rw [weighted_fiber,ContinuousLinearMap.smul_apply,FiniteSum.fiber_smul,fiber_amplify]

theorem rejection_coefficient (h : Density) (g : Fin 4) (x y : Fin 5) (a b : Fin 6)
    (hr : Compiler.conditionalFmsRule x.val y.val a.val b.val=false) :
    (alice g x).effect a*root (density h)*transpose ((bob g y).effect b)=0 := by
  change amplify 3 (scalarOp 17 ((CompilerHonestFamilies.alice g x).effect a))*root (density h)*
    transpose (amplify 3 (scalarOp 17 ((CompilerHonestFamilies.bob g y).effect b)))=0
  rw [density_root,transpose_amplify,mul_smul_comm,smul_mul_assoc,
    ← amplify_mul,← amplify_mul,scaffold_rejection h g x y a b hr,amplify_zero_eq]
  exact CompilerAlgebra.op_smul_zero _

/-- These are actual vector equations on the common state, rather than only
scalar matrix identities. -/
theorem rejection (h : Density) (g : Fin 4) (x y : Fin 5) (a b : Fin 6)
    (hr : Compiler.conditionalFmsRule x.val y.val a.val b.val=false) :
    (TensorLifts.left ((alice g x).effect a)*TensorLifts.right ((bob g y).effect b))
      (vector (density h))=0 :=
  event_zero _ _ _ (rejection_coefficient h g x y a b hr)

#print axioms scaffold_root
#print axioms scaffold_rejection
#print axioms density_root
#print axioms rejection
end Sigma2.CompilerHonestFMSLift
