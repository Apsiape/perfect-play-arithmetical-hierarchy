import Sigma2.RowGlobalXEntries

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates CoarseCells RowColumns RowWalsh

/-- Literal coefficients of a Walsh operator in the same supported blocks. -/
theorem fourierUnit_blocks {d : ℕ} (n : ℕ) (P : Op) (t : Fin d → Fin d → Op)
    (hu : Units P t) (o a i j : Fin d) :
    matrixBlocks hu o (fourierUnit n t a) i j=
      ((1/(d:ℂ))*sign (parity n a.val i.val)*sign (parity n a.val j.val)) • t o o := by
  simp only [fourierUnit,MatrixBlocks.sum,MatrixBlocks.smul,MatrixBlocks.unit,
    Matrix.sum_apply,Matrix.smul_apply]
  have hz (c : ℂ) : c • (0:Op)=0 := by module
  simp [Matrix.single_apply,smul_ite,hz,ite_and]

/-- The actual zero X outcome is the uniform reference on either supplied
    original marginal support, with the actual 00 corner as its coefficient. -/
theorem globalX_zero_blocks (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (i j : Fin (RowSlots.dimension R)) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    matrixBlocks hu 0 (newEffects bob G R S.measurements P (globalQ R true) (scalarAnswer G R 0)) i j=
      (1/(RowSlots.dimension R:ℂ)) • numericalUnit bob G R S.measurements P 0 0 := by
  dsimp only
  rw [globalX_fourier bob G R S hS h hm P hP,fourierUnit_blocks]
  simp [RowParity.parity_zero,sign]

/-- Remove exactly the invalid padded answers from any finite sum. -/
theorem scalarAnswer_sum (G : Game) (R : Rows G.scenario) (F : Answer G R → Op)
    (hz : ∀ a,RowSlots.dimension R≤a.val → F a=0) :
    (∑ a,F a)=∑ i : Fin (RowSlots.dimension R),F (scalarAnswer G R i) := by
  symm
  apply Finset.sum_of_injOn (scalarAnswer G R)
  · intro i _ j _ hij
    apply Fin.ext
    exact congrArg (fun a : Answer G R => a.val) hij
  · intro i _; exact Finset.mem_univ _
  · intro b _ hb
    apply hz b
    by_contra hn
    have hlt : b.val<RowSlots.dimension R := by omega
    apply hb
    exact ⟨⟨b.val,hlt⟩,Finset.mem_univ _,Fin.ext rfl⟩
  · intro i _; rfl

#print axioms fourierUnit_blocks
#print axioms globalX_zero_blocks
#print axioms scalarAnswer_sum
end Sigma2.RowScalar