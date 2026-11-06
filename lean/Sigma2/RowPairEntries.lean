import Sigma2.RowParityEntries
import Mathlib.Data.Matrix.Basis

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates CoarseCells RowColumns RowWalsh

/-- The canonical pair difference is the actual X parity times its proved
    two-point Z sector. -/
theorem pair_K_factor (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) :
    pairJoint bob G R S.measurements P j 0-pairJoint bob G R S.measurements P j 1=
      actualXParity bob G R S.measurements P j*
        (numericalUnit bob G R S.measurements P 0 0+
          numericalUnit bob G R S.measurements P ⟨j,hj.2⟩ ⟨j,hj.2⟩) := by
  let a0 := sixAnswer G R 0
  let a1 := sixAnswer G R 1
  have h0 := pair_coset_formula bob G R S hS h hm P hP j hj a0 (by
    have := RowSlots.dimension_pos R; simp [a0,sixAnswer,valid]; omega)
  have h1 := pair_coset_formula bob G R S hS h hm P hP j hj a1 (by
    have := RowSlots.dimension_pos R; simp [a1,sixAnswer,valid]; omega)
  rw [pair_unique bob G R S hS h hm P hP] at h0 h1
  simp only [a0,a1,sixAnswer,Fin.val_zero,Fin.val_one,Nat.zero_mod,Nat.zero_div,
    Nat.reduceMod,Nat.reduceDiv,Nat.xor_eq,Nat.zero_xor,
    show decide ((0:ℕ)=1)=false from rfl,decide_true] at h0 h1
  have hz := (pair_active_sector bob G R S hS h hm P hP j hj).symm.trans
    (pair_D_diagonal bob G R S hS h hm P hP j hj)
  rw [h0,h1,← sub_mul,hz]
  rfl

theorem actualXParity_supported (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (hP : Projection P) (mask : ℕ) :
    actualXParity bob G R M P mask*P=actualXParity bob G R M P mask := by
  unfold actualXParity
  rw [sub_mul,(new_coarse_supported bob G R M P hP _ _ false).2,
    (new_coarse_supported bob G R M P hP _ _ true).2]

theorem matrix_mul_single_entry {d : ℕ} (M : Matrix (Fin d) (Fin d) Op)
    (a b i j : Fin d) (e : Op) :
    (M*Matrix.single a b e) i j=if j=b then M i a*e else 0 := by
  by_cases hj : j=b
  · subst j; simp
  · simp [hj]

/-- Both canonical K_j transition blocks are literal 0j and j0 entries,
    on either original support and in the fixed numerical scalar units. -/
theorem pair_K_blocks (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    let e := numericalUnit bob G R S.measurements P 0 0
    matrixBlocks hu 0 (pairJoint bob G R S.measurements P j 0-pairJoint bob G R S.measurements P j 1)=
      Matrix.single ⟨j,hj.2⟩ 0 e+Matrix.single 0 ⟨j,hj.2⟩ e := by
  dsimp only
  let hu := numericalUnit_laws bob G R S hS h hm P hP
  let e := numericalUnit bob G R S.measurements P 0 0
  rw [pair_K_factor bob G R S hS h hm P hP j hj,
    MatrixBlocks.mul _ _ _ _ (actualXParity_supported bob G R S.measurements P hP.1 j),
    MatrixBlocks.add,MatrixBlocks.unit,MatrixBlocks.unit,Matrix.mul_add]
  apply Matrix.ext
  intro i l
  simp only [Matrix.add_apply,matrix_mul_single_entry]
  rw [actualXParity_blocks bob G R S hS h hm P hP ⟨j,hj.2⟩ i 0,
    actualXParity_blocks bob G R S hS h hm P hP ⟨j,hj.2⟩ i ⟨j,hj.2⟩]
  have hx0 : Nat.xor j i.val=0 ↔ i=⟨j,hj.2⟩ := by
    constructor
    · intro he
      have hh := congrArg (fun a => Nat.xor j a) he
      simp only [Nat.xor_eq,Nat.xor_xor_cancel_left,Nat.xor_zero] at hh
      exact Fin.ext hh
    · intro he; subst i; simp [Nat.xor_eq]
  have hxj : Nat.xor j i.val=j ↔ i=0 := by
    constructor
    · intro he
      have hh := congrArg (fun a => Nat.xor j a) he
      simp only [Nat.xor_eq,Nat.xor_xor_cancel_left,Nat.xor_self] at hh
      exact Fin.ext hh
    · intro he; subst i; simp [Nat.xor_eq]
  simp only [Fin.val_mk,Fin.val_zero,hx0,hxj]
  have he : e*e=e := (hu.diagonal_projection 0).2
  have hmul (p : Prop) [Decidable p] : (if p then e else 0)*e=if p then e else 0 := by
    split_ifs <;> simp only [he,zero_mul]
  have hs1 : (Matrix.single (⟨j,hj.2⟩ : Fin (RowSlots.dimension R)) 0 e) i l=
      if l=0 then if i=⟨j,hj.2⟩ then e else 0 else 0 := by
    by_cases hi : i=⟨j,hj.2⟩ <;> by_cases hl : l=0 <;> simp [Matrix.single_apply,hi,hl,eq_comm]
  have hs2 : (Matrix.single 0 (⟨j,hj.2⟩ : Fin (RowSlots.dimension R)) e) i l=
      if l=⟨j,hj.2⟩ then if i=0 then e else 0 else 0 := by
    by_cases hi : i=0 <;> by_cases hl : l=⟨j,hj.2⟩ <;> simp [Matrix.single_apply,hi,hl,eq_comm]
  change (if l=0 then (if i=⟨j,hj.2⟩ then e else 0)*e else 0)+
      (if l=⟨j,hj.2⟩ then (if i=0 then e else 0)*e else 0)=
      (Matrix.single ⟨j,hj.2⟩ 0 e) i l+(Matrix.single 0 ⟨j,hj.2⟩ e) i l
  rw [hs1,hs2]
  simp only [hmul]

#print axioms pair_K_factor
#print axioms actualXParity_supported
#print axioms matrix_mul_single_entry
#print axioms pair_K_blocks
end Sigma2.RowScalar