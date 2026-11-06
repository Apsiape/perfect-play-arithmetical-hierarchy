import Sigma2.RowFourierEntries

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates CoarseCells FiniteJoint RowColumns RowWalsh TensorLifts MirrorUnits

/-- Numerical form of the actual X-bit action in the original scalar units. -/
theorem measured_X_numerical_action (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (k : Fin (2*RowSlots.squares R)) (i j : Fin (RowSlots.dimension R)) :
    binary G R S.measurements P (bitAxis R true k)*numericalUnit false G R S.measurements P i j=
      numericalUnit false G R S.measurements P
        ⟨Nat.xor i.val (2^k.val),by
          exact lt_of_lt_of_eq (RowParity.xor_bound (lt_of_lt_of_eq i.isLt (dimension_bits R))
            (Nat.pow_lt_pow_right (by decide) k.isLt)) (dimension_bits R).symm⟩ j := by
  let g : Fin (RowSlots.squares R) := ⟨k.val/2,by have := k.isLt; omega⟩
  let l : Fin 2 := ⟨k.val%2,Nat.mod_lt _ (by decide)⟩
  have hk : 2*g.val+l.val=k.val := by dsimp [g,l]; omega
  have hf : registerFlip g l ((registerFin _).symm i)=
      (registerFin _).symm ⟨Nat.xor i.val (2^k.val),by
        change Nat.xor i.val (2^k.val)<RowSlots.dimension R
        exact lt_of_lt_of_eq (RowParity.xor_bound (lt_of_lt_of_eq i.isLt (dimension_bits R))
          (Nat.pow_lt_pow_right (by decide) k.isLt)) (dimension_bits R).symm⟩ := by
    apply (registerFin _).injective
    apply Fin.ext
    rw [registerFin_flip,hk,Equiv.apply_symm_apply,Equiv.apply_symm_apply]
  have hh := measured_X_tensor_action G R S hS h hm P hP g l ((registerFin _).symm i) ((registerFin _).symm j)
  rw [hf] at hh
  exact hh

/-- The complete actual X measurement has the literal Walsh coefficients,
    with no replacement coordinate representation or extra hypothesis. -/
theorem globalX_fourier_alice (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (a : Fin (RowSlots.dimension R)) :
    newEffects false G R S.measurements P (globalQ R true) (scalarAnswer G R a)=
      fourierUnit (2*RowSlots.squares R) (numericalUnit false G R S.measurements P) a := by
  rw [global_unique false G R S hS h hm P hP]
  simp only [globalJoint,scalarAnswer,a.isLt,ite_true]
  have he : (fun k : Fin (2*RowSlots.squares R) =>
      axisEffect false G R S.measurements P true k (Nat.testBit a.val k.val))=
      (fun k => (1/2:ℂ) • (P+sign (Nat.testBit a.val k.val) • binary G R S.measurements P (bitAxis R true k))) := by
    funext k
    rw [axis_effect_formula false G R S hS h hm P hP]
    rfl
  rw [he]
  exact fourierUnit_joint _ (dimension_bits R) P _ (numericalUnit_laws false G R S hS h hm P hP)
    _ (measured_X_numerical_action G R S hS h hm P hP) a

#print axioms measured_X_numerical_action
#print axioms globalX_fourier_alice
/-- The Fourier fine operator is supported on the same original support. -/
theorem fourierUnit_supported {d : ℕ} (n : ℕ) (P : Op) (t : Fin d → Fin d → Op)
    (hu : Units P t) (a : Fin d) : fourierUnit n t a*P=fourierUnit n t a := by
  simp only [fourierUnit,Finset.sum_mul,smul_mul_assoc,(hu.supported _ _).2]

/-- Bob's reversed common units give the same Walsh coefficients, while
    keeping his supplied original marginal under purification. -/
theorem globalX_fourier_bob (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q)
    (a : Fin (RowSlots.dimension R)) :
    newEffects true G R S.measurements Q (globalQ R true) (scalarAnswer G R a)=
      fourierUnit (2*RowSlots.squares R) (numericalUnit true G R S.measurements Q) a := by
  obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
  have hT := pure_perfect_transfer G R S hS T hprob
  obtain ⟨hA,_,hmA,_⟩ := marginals_exist (normalOfPure T)
  obtain ⟨P,hP⟩ := support_exists hA
  have he : newEffects true G R T.measurements Q (globalQ R true) (scalarAnswer G R a)=
      fourierUnit (2*RowSlots.squares R) (numericalUnit true G R T.measurements Q) a := by
    apply right_local_eq T h (hM h hm) Q hQ _ _
      (new_fine_supported true G R T.measurements Q hQ.1 _ _).2
      (fourierUnit_supported _ Q _ (numericalUnit_laws true G R (normalOfPure T) hT h (hM h hm) Q hQ) a)
    calc
      _ = left (newEffects false G R T.measurements P (globalQ R true) (scalarAnswer G R a)) T.vector :=
        (pure_new_fine_mirror G R T hT hA h hmA (hM h hm) P Q hP hQ _ _).symm
      _ = left (fourierUnit (2*RowSlots.squares R) (numericalUnit false G R T.measurements P) a) T.vector := by
        rw [show newEffects false G R T.measurements P (globalQ R true) (scalarAnswer G R a)=
          fourierUnit (2*RowSlots.squares R) (numericalUnit false G R T.measurements P) a from
            globalX_fourier_alice G R (normalOfPure T) hT hA hmA P hP a]
      _ = right (fourierUnit (2*RowSlots.squares R) (numericalUnit true G R T.measurements Q) a) T.vector := by
        unfold fourierUnit
        conv_rhs => rw [Finset.sum_comm]
        simp only [left_sum,right_sum,sum_apply,MagicRelations.left_smul,MagicRelations.right_smul,smul_apply]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hh := (common_units_mirror G R T hT hA h hmA (hM h hm) P Q hP hQ
          ((registerFin _).symm i) ((registerFin _).symm j)).1
        change _ • left (tensorUnit P (localUnit G R T.measurements P)
          ((registerFin _).symm i) ((registerFin _).symm j)) T.vector=_
        rw [hh]
        congr 1
        ring
  have hl : bobLocal G R T.measurements Q=bobLocal G R S.measurements Q := by
    funext g i j
    simp only [bobLocal,bobBinary,hB,Purification.measurements,TensorLifts.measurements]
  simp only [fourierUnit,numericalUnit,supportUnits,ite_true,bobTensor] at he
  rw [hl] at he
  simpa only [newEffects,ite_true,hB,Purification.measurements,TensorLifts.measurements,
    fourierUnit,numericalUnit,supportUnits,ite_true,bobTensor] using he

/-- Both actual original supports share the same literal Fourier entries. -/
theorem globalX_fourier (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (a : Fin (RowSlots.dimension R)) :
    newEffects bob G R S.measurements P (globalQ R true) (scalarAnswer G R a)=
      fourierUnit (2*RowSlots.squares R) (numericalUnit bob G R S.measurements P) a := by
  cases bob
  · exact globalX_fourier_alice G R S hS h hm P hP a
  · exact globalX_fourier_bob G R S hS h hm P hP a

#print axioms fourierUnit_supported
#print axioms globalX_fourier_bob
#print axioms globalX_fourier
end Sigma2.RowScalar