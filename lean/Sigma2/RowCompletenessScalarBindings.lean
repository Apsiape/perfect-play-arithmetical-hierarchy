import Sigma2.RowCompletenessAxisBindings

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns RowWalsh FiniteAncilla

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem right_eigen_of_left (A U : Op) (hA : star A=A) (hU : star U=U) (b : Bool)
    (he : U*A=sign b • A) : A*U=sign b • A := by
  have hh := congrArg star he
  simpa only [star_mul,hA,hU,star_smul,sign_star] using hh

theorem realize_reflection (n : ℕ) (U : Matrix (Fin (2^n)) (Fin (2^n)) Op)
    (b : Bool) : matrixOp (2^n) ((1/2:ℂ) • (1+sign b • U))=
      spectralEffect (matrixOp (2^n) U) b := by
  rw [matrixOp_smul,matrixOp_add,matrixOp_one,matrixOp_smul]
  rfl

theorem globalZ_eigen (n : ℕ) (r : Fin (2^n)) (k : Fin n) :
    (realizePartition (diagonalPartition (2^n))).effect r*scalarZ n k=
      sign (Nat.testBit r.val k.val) • (realizePartition (diagonalPartition (2^n))).effect r := by
  apply right_eigen_of_left _ _ ((realizePartition (diagonalPartition (2^n))).selfadjoint r) (scalarZ_star n k)
  change matrixOp _ _*matrixOp _ _=_
  rw [← matrixOp_mul,phase_diagonal,matrixOp_smul,RowParity.parity_single n k.val r.val k.isLt]
  rfl

theorem globalX_eigen (n : ℕ) (r : Fin (2^n)) (k : Fin n) :
    (realizePartition (fourierPartition n)).effect r*scalarX n k=
      sign (Nat.testBit r.val k.val) • (realizePartition (fourierPartition n)).effect r := by
  apply right_eigen_of_left _ _ ((realizePartition (fourierPartition n)).selfadjoint r) (scalarX_star n k)
  change matrixOp _ _*matrixOp _ _=_
  rw [← matrixOp_mul,shift_fourier,matrixOp_smul,RowParity.parity_single n k.val r.val k.isLt]
  rfl

theorem global_axis {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (isX : Bool) (k : Fin 2) :
    rowAxis R g ⟨k.val+if isX then 2 else 0,by split <;> have := k.isLt <;> omega⟩=
      if isX then scalarX (bits R) (squareBit R g k) else scalarZ (bits R) (squareBit R g k) := by
  cases isX <;> fin_cases k <;> rfl

theorem global_binding_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (isX : Bool) (g : Fin (RowSlots.squares R)) (k : Fin 2)
    (a b : AA (scenario G R)) (ha : a.val<RowSlots.dimension R) (hb : b.val<2)
    (hne : b.val≠bitAnswer (Nat.testBit a.val (2*g.val+k.val))) :
    (newPartition G R E hE (.global isX)).effect a*
      (newPartition G R E hE (axis R g ⟨k.val+if isX then 2 else 0,by split <;> have := k.isLt <;> omega⟩)).effect b=0 := by
  obtain ⟨t,hb⟩ := decode_cell_answer b.val hb
  let ax : Fin 4 := ⟨k.val+if isX then 2 else 0,by split <;> have := k.isLt <;> omega⟩
  rw [axis_effect G R E hE g ax t b hb,global_axis R g isX k]
  have har : a.val<2^(bits R) := by simpa only [RowScalar.dimension_bits] using ha
  let r : Fin (2^(bits R)) := ⟨a.val,har⟩
  have ht : Nat.testBit a.val (2*g.val+k.val)≠t := by
    intro he; apply hne; rw [hb,he]
  cases isX
  · rw [globalZ_effect G R E hE r a rfl]
    exact (spectral_action _ _ (scalarZ_star _ _) (scalarZ_square _ _) _ t (globalZ_eigen _ r (squareBit R g k))).trans (if_neg ht)
  · rw [globalX_effect G R E hE r a rfl]
    exact (spectral_action _ _ (scalarX_star _ _) (scalarX_square _ _) _ t (globalX_eigen _ r (squareBit R g k))).trans (if_neg ht)

theorem decode_pair_answer (n v : ℕ) (hv : v<2*2^n) :
    ∃ b : Bool,∃ r : Fin (2^n),v=2*r.val+bit b := by
  have hmod := Nat.mod_lt v (by decide : 0<2)
  have hr : v/2<2^n := by omega
  by_cases he : v%2=0
  · exact ⟨false,⟨v/2,hr⟩,by simp only [bit,Bool.false_eq_true,ite_false]; omega⟩
  · exact ⟨true,⟨v/2,hr⟩,by simp only [bit,Bool.true_eq,ite_true]; omega⟩

theorem spectral_action_left (A U : Op) (hs : star U=U) (hq : U*U=1) (s b : Bool)
    (he : U*A=sign s • A) : spectralEffect U b*A=if s=b then A else 0 := by
  change ((1/2:ℂ) • (1+sign b • U))*A=_
  rw [smul_mul_assoc,add_mul,one_mul,smul_mul_assoc,he,smul_smul]
  cases s <;> cases b <;> norm_num [sign]
  all_goals module

theorem pair_fourier_zero (n j : ℕ) (hj : j<2^n) (b : Bool) (r t : Fin (2^n))
    (hne : b≠parity n j t.val) :
    (realizePartition (pairPartition n j hj)).effect (b,r)*
      (realizePartition (fourierPartition n)).effect t=0 := by
  let D := ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect r
  let U := matrixOp (2^n) (shift n j hj)
  let A := (realizePartition (fourierPartition n)).effect t
  have he : U*A=sign (parity n j t.val) • A := by
    dsimp only [U,A,realizePartition]
    rw [← matrixOp_mul,shift_fourier,matrixOp_smul]
  have hc : Commute U (matrixOp (2^n) D) := by
    change matrixOp _ _*matrixOp _ _=matrixOp _ _*matrixOp _ _
    rw [← matrixOp_mul,← matrixOp_mul]
    exact congrArg (matrixOp (2^n)) (shift_coset_commute n j hj r)
  have hs : star U=U := by dsimp only [U]; rw [← matrixOp_star,shift_star]
  have hq : U*U=1 := by dsimp only [U]; rw [← matrixOp_mul,shift_square,matrixOp_one]
  change matrixOp _ (((1/2:ℂ) • (1+sign b • shift n j hj))*D)*A=0
  rw [matrixOp_mul,realize_reflection]
  change (spectralEffect U b*matrixOp _ D)*A=0
  rw [← (commute_spectral (matrixOp _ D) U hc.symm b).eq,mul_assoc,
    spectral_action_left A U hs hq _ b he,if_neg (Ne.symm hne),mul_zero]

theorem pair_X_binding_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (j : ℕ) (hj : j<2^(bits R))
    (a b : AA (scenario G R)) (ha : a.val<2*RowSlots.dimension R) (hb : b.val<RowSlots.dimension R)
    (hne : decide (a.val%2=1)≠parity (bits R) j b.val) :
    (newPartition G R E hE (.pair j)).effect a*(newPartition G R E hE (.global true)).effect b=0 := by
  have har : a.val<2*2^(bits R) := by simpa only [RowScalar.dimension_bits] using ha
  have hbr : b.val<2^(bits R) := by simpa only [RowScalar.dimension_bits] using hb
  obtain ⟨neg,r,ha⟩ := decode_pair_answer (bits R) a.val har
  rw [pair_effect G R E hE j hj (neg,r) a ha,globalX_effect G R E hE ⟨b.val,hbr⟩ b rfl]
  apply pair_fourier_zero
  have hbit : decide ((2*r.val+bit neg)%2=1)=neg := by cases neg <;> simp [bit]
  simpa only [ha,hbit] using hne

end Sigma2.RowCompleteness
