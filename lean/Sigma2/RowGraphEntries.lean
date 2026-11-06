import Sigma2.RowPairEntries
import Sigma2.RowActualColumnCoordinates
import Sigma2.RowColumnGeometry

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates RowColumns RowWalsh

/-- Multiplication by a scalar-commuting operator changes just the corner
    coefficient of a single matrix unit. -/
theorem central_unit_blocks {d : ℕ} (P : Op) (t : Fin d → Fin d → Op)
    (hu : Units P t) (o : Fin d) (A : Op) (hc : ∀ i j,Commute A (t i j)) (k l : Fin d) :
    matrixBlocks hu o (A*t k l)=Matrix.single k l (A*t o o) := by
  apply Matrix.ext
  intro i j
  have he : matrixBlocks hu o (A*t k l) i j=A*matrixBlocks hu o (t k l) i j := by
    change t o i*(A*t k l)*t j o=A*(t o i*t k l*t j o)
    rw [← mul_assoc (t o i) A,← (hc o i).eq]
    noncomm_ring
  rw [he,MatrixBlocks.unit]
  by_cases hik : i=k <;> by_cases hjl : j=l <;>
    simp [Matrix.single_apply,hik,hjl,eq_comm]

theorem diagonal_single {d : ℕ} (e A : Op) (k l : Fin d) :
    Matrix.diagonal (fun _ => e)*Matrix.single k l A=Matrix.single k l (e*A) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.diagonal_mul]
  by_cases hik : i=k <;> by_cases hjl : j=l <;>
    simp [Matrix.single_apply,hik,hjl,eq_comm]

/-- Complex scalar multiplication through the finite block product. -/
theorem complex_matrix_mul_smul {d : ℕ} (M N : Matrix (Fin d) (Fin d) Op) (c : ℂ) :
    M*(c • N)=c • (M*N) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply,Matrix.smul_apply,mul_smul_comm,Finset.smul_sum]
theorem slotCornerUnitary_selfadjoint (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) :
    star (slotCornerUnitary bob G R S.measurements P r j)=slotCornerUnitary bob G R S.measurements P r j := by
  have hu := numericalUnit_laws bob G R S hS h hm P hP
  rw [slotCornerUnitary,star_add (slotReflection bob G R S.measurements P r j*numericalUnit bob G R S.measurements P 0 0) (1-numericalUnit bob G R S.measurements P 0 0),star_mul,star_sub (1:Op) _,star_one,(hu.diagonal_projection 0).1,
    (slotReflection_laws bob G R S hS h hm P hP r j).1]
  rw [← (slotReflection_numerical_commute bob G R S hS h hm P hP r j 0 0).eq]

theorem slotCornerUnitary_corner (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) :
    numericalUnit bob G R S.measurements P 0 0*slotCornerUnitary bob G R S.measurements P r j=
      slotReflection bob G R S.measurements P r j*numericalUnit bob G R S.measurements P 0 0 := by
  have hu := numericalUnit_laws bob G R S hS h hm P hP
  let e := numericalUnit bob G R S.measurements P 0 0
  have he : e*e=e := (hu.diagonal_projection 0).2
  have hc := slotReflection_numerical_commute bob G R S hS h hm P hP r j 0 0
  change e*(slotReflection bob G R S.measurements P r j*e+(1-e))=_
  rw [mul_add,← mul_assoc,← hc.eq,mul_assoc,he,mul_sub,mul_one,he,sub_self,add_zero]

/-- Every actual slot graph is the supported normalized matrixGraph required
    by the uniqueness theorem, with its actual reflection coefficient. -/
theorem slot_graph_blocks (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (eps : Bool) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    let e := numericalUnit bob G R S.measurements P 0 0
    matrixBlocks hu 0 (slotGraph bob G R S.measurements P r j hj eps)=
      Matrix.diagonal (fun _ => e)*matrixGraph 0 ⟨j,hj.2⟩
        (slotCornerUnitary bob G R S.measurements P r j) eps := by
  dsimp only
  let hu := numericalUnit_laws bob G R S hS h hm P hP
  have hK := pair_K_blocks bob G R S hS h hm P hP j hj
  have huK : pairJoint bob G R S.measurements P j 0-pairJoint bob G R S.measurements P j 1=
      numericalUnit bob G R S.measurements P ⟨j,hj.2⟩ 0+
        numericalUnit bob G R S.measurements P 0 ⟨j,hj.2⟩ := by
    let K := pairJoint bob G R S.measurements P j 0-pairJoint bob G R S.measurements P j 1
    have hXL : P*actualXParity bob G R S.measurements P j=actualXParity bob G R S.measurements P j := by
      unfold actualXParity
      rw [mul_sub,(new_coarse_supported bob G R S.measurements P hP.1 _ _ false).1,
        (new_coarse_supported bob G R S.measurements P hP.1 _ _ true).1]
    have hKL : P*K=K := by
      dsimp only [K]
      rw [pair_K_factor bob G R S hS h hm P hP j hj,← mul_assoc,hXL]
    have hKR : K*P=K := by
      dsimp only [K]
      rw [pair_K_factor bob G R S hS h hm P hP j hj,mul_assoc,add_mul,
        (hu.supported 0 0).2,(hu.supported ⟨j,hj.2⟩ ⟨j,hj.2⟩).2]
    change K=_
    apply sub_eq_zero.mp
    apply MatrixBlocks.eq_zero hu 0
    · simp only [mul_sub,hKL,mul_add,(hu.supported _ _).1]
    · simp only [sub_mul,hKR,add_mul,(hu.supported _ _).2]
    · rw [MatrixBlocks.sub,hK,MatrixBlocks.add,MatrixBlocks.unit,MatrixBlocks.unit,sub_self]
  rw [slot_graph_formula bob G R S hS h hm P hP r j hj eps,
    pair_D_diagonal bob G R S hS h hm P hP j hj,huK,mul_add,
    MatrixBlocks.smul,MatrixBlocks.add,MatrixBlocks.smul,MatrixBlocks.add,
    MatrixBlocks.add,MatrixBlocks.unit,MatrixBlocks.unit,
    central_unit_blocks P _ hu 0 _ (slotReflection_numerical_commute bob G R S hS h hm P hP r j),
    central_unit_blocks P _ hu 0 _ (slotReflection_numerical_commute bob G R S hS h hm P hP r j)]
  simp only [matrixGraph,complex_matrix_mul_smul,Matrix.mul_add,diagonal_single,mul_one,
    slotCornerUnitary_selfadjoint bob G R S hS h hm P hP,
    slotCornerUnitary_corner bob G R S hS h hm P hP]

#print axioms complex_matrix_mul_smul
#print axioms central_unit_blocks
#print axioms diagonal_single
#print axioms slotCornerUnitary_selfadjoint
#print axioms slotCornerUnitary_corner
#print axioms slot_graph_blocks
end Sigma2.RowScalar