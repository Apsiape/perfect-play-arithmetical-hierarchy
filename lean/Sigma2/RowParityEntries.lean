import Sigma2.RowXBlocks

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates CoarseCells RowColumns RowWalsh

/-- The signed parity of the complete actual X measurement. -/
def actualXParity (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (mask : ℕ) : Op :=
  coarse (newEffects bob G R M P (globalQ R true)) (fun a => parity (2*RowSlots.squares R) mask a.val) false-
    coarse (newEffects bob G R M P (globalQ R true)) (fun a => parity (2*RowSlots.squares R) mask a.val) true

theorem actualXParity_sum (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P) (mask : ℕ) :
    actualXParity bob G R S.measurements P mask=
      ∑ a : Fin (RowSlots.dimension R),sign (parity (2*RowSlots.squares R) mask a.val) •
        fourierUnit (2*RowSlots.squares R) (numericalUnit bob G R S.measurements P) a := by
  let X := newEffects bob G R S.measurements P (globalQ R true)
  have he : actualXParity bob G R S.measurements P mask=
      ∑ a : Answer G R,sign (parity (2*RowSlots.squares R) mask a.val) • X a := by
    unfold actualXParity coarse
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    cases hp : parity (2*RowSlots.squares R) mask a.val <;> simp [hp,sign,X] <;> module
  rw [he,scalarAnswer_sum G R _ (by
    intro a ha
    have hz := new_invalid_zero bob G R S hS h hm P hP (globalQ R true) a (by simp [globalQ,valid,show ¬a.val<RowSlots.dimension R by omega])
    simp only [X,hz]; module)]
  apply Finset.sum_congr rfl
  intro a _
  rw [show X (scalarAnswer G R a)=fourierUnit (2*RowSlots.squares R) (numericalUnit bob G R S.measurements P) a from
    globalX_fourier bob G R S hS h hm P hP a]
  rfl

/-- A Fourier-weighted parity is exactly the numerical xor transition. -/
theorem fourierParity_blocks {d : ℕ} (n : ℕ) (hd : d=2^n) (P : Op)
    (t : Fin d → Fin d → Op) (hu : Units P t) (o mask i j : Fin d) :
    matrixBlocks hu o (∑ a : Fin d,sign (parity n mask.val a.val) • fourierUnit n t a) i j=
      if Nat.xor mask.val i.val=j.val then t o o else 0 := by
  subst d
  let u : Fin (2^n) := ⟨Nat.xor mask.val i.val,RowParity.xor_bound mask.isLt i.isLt⟩
  simp only [MatrixBlocks.sum,MatrixBlocks.smul,Matrix.sum_apply,Matrix.smul_apply,fourierUnit_blocks,smul_smul]
  have he (a : Fin (2^n)) :
      sign (parity n mask.val a.val)*((1/((2^n:ℕ):ℂ))*sign (parity n a.val i.val)*sign (parity n a.val j.val))=
        (1/((2^n:ℕ):ℂ))*(sign (parity n a.val u.val)*sign (parity n a.val j.val)) := by
    dsimp only [u]
    rw [parity_symm n mask.val a.val,parity_right_xor,sign_xor]
    ring
  simp_rw [he]
  rw [← Finset.sum_smul,← Finset.mul_sum,character_orthogonality]
  have hn : ((2^n:ℕ):ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.two_pow_pos n))
  have heq : u=j ↔ Nat.xor mask.val i.val=j.val := Fin.ext_iff
  simp only [← heq]
  by_cases hij : u=j <;> simp [hij,hn]

theorem actualXParity_blocks (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (mask i j : Fin (RowSlots.dimension R)) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    matrixBlocks hu 0 (actualXParity bob G R S.measurements P mask.val) i j=
      if Nat.xor mask.val i.val=j.val then numericalUnit bob G R S.measurements P 0 0 else 0 := by
  dsimp only
  rw [actualXParity_sum bob G R S hS h hm P hP]
  exact fourierParity_blocks _ (dimension_bits R) P _ _ 0 mask i j

#print axioms actualXParity_sum
#print axioms fourierParity_blocks
#print axioms actualXParity_blocks
end Sigma2.RowScalar