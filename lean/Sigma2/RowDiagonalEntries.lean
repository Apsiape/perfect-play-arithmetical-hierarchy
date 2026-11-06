import Sigma2.RowGlobalZEntries

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates CoarseCells TensorLifts MirrorUnits

instance rowDimensionNeZero {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨Nat.ne_of_gt (RowSlots.dimension_pos R)⟩

/-- Exact fine-effect mirror for any actual synchronized new question. -/
theorem pure_new_fine_mirror (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (hA hB : Density) (hmA : MarginalA (normalOfPure S) hA) (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (q : NewQ R) (a : Answer G R) :
    left (newEffects false G R S.measurements P q a) S.vector=
      right (newEffects true G R S.measurements Q q a) S.vector := by
  have hh := (RowSynchronization.pure_binary_analysis S ⟨qa G R q,qb G R q,a,a⟩ hA hmA P hP
    (new_synchronized G R (normalOfPure S) hS q a)).1
  have hm : left (S.measurements.alice (qa G R q) a) S.vector=
      right (S.measurements.bob (qb G R q) a) S.vector := by
    simpa only [measurements_left,measurements_right] using hh
  exact MirrorAlgebra.compressed_mirror S.vector P Q _ _
    (MirrorAlgebra.left_support S hA hmA P hP) (MirrorAlgebra.right_support S hB hmB Q hQ) hm

/-- Bob uses the already constructed transposed, reversed common units.
    His supplied original marginal and support survive the purification. -/
theorem globalZ_diagonal_bob (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q)
    (a : Fin (RowSlots.dimension R)) :
    newEffects true G R S.measurements Q (globalQ R false) (scalarAnswer G R a)=
      bobTensor G R S.measurements Q ((registerFin _).symm a) ((registerFin _).symm a) := by
  obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
  have hT := pure_perfect_transfer G R S hS T hprob
  obtain ⟨hA,_,hmA,_⟩ := marginals_exist (normalOfPure T)
  obtain ⟨P,hP⟩ := support_exists hA
  let b := (registerFin (RowSlots.squares R)).symm a
  have he : newEffects true G R T.measurements Q (globalQ R false) (scalarAnswer G R a)=
      bobTensor G R T.measurements Q b b := by
    apply right_local_eq T h (hM h hm) Q hQ _ _
      (new_fine_supported true G R T.measurements Q hQ.1 _ _).2
      (bobTensor_supported G R T.measurements Q hQ.1 b b).2
    calc
      _ = left (newEffects false G R T.measurements P (globalQ R false) (scalarAnswer G R a)) T.vector :=
        (pure_new_fine_mirror G R T hT hA h hmA (hM h hm) P Q hP hQ _ _).symm
      _ = left (tensorUnit P (localUnit G R T.measurements P) b b) T.vector := by
        apply congrArg (fun A : Op => left A T.vector)
        simpa only [normalOfPure] using globalZ_diagonal_alice G R (normalOfPure T) hT hA hmA P hP a
      _ = right (bobTensor G R T.measurements Q b b) T.vector :=
        (common_units_mirror G R T hT hA h hmA (hM h hm) P Q hP hQ b b).1
  have hl : bobLocal G R T.measurements Q=bobLocal G R S.measurements Q := by
    funext g i j
    simp only [bobLocal,bobBinary,hB,Purification.measurements,TensorLifts.measurements]
  dsimp only [bobTensor] at he
  rw [hl] at he
  simpa only [newEffects,ite_true,hB,Purification.measurements,TensorLifts.measurements,bobTensor,b] using he

/-- Both parties' actual Z effects, in exactly the common units of step 1. -/
theorem globalZ_diagonal (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (a : Fin (RowSlots.dimension R)) :
    newEffects bob G R S.measurements P (globalQ R false) (scalarAnswer G R a)=
      supportUnits bob G R S.measurements P ((registerFin _).symm a) ((registerFin _).symm a) := by
  cases bob
  · exact globalZ_diagonal_alice G R S hS h hm P hP a
  · exact globalZ_diagonal_bob G R S hS h hm P hP a

/-- Numerical labels for the same support units; no new representation. -/
def numericalUnit (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (i j : Fin (RowSlots.dimension R)) : Op :=
  supportUnits bob G R M P ((registerFin _).symm i) ((registerFin _).symm j)

theorem numericalUnit_laws (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P) :
    Units P (numericalUnit bob G R S.measurements P) := by
  have hu := supportUnits_laws bob G R S hS h hm P hP
  refine ⟨?_,?_,?_⟩
  · intro i j k l
    simp only [numericalUnit,hu.product,(registerFin _).symm.injective.eq_iff]
    split_ifs <;> simp_all
  · intro i j; exact hu.adjoint _ _
  · change (∑ i,supportUnits bob G R S.measurements P ((registerFin _).symm i) ((registerFin _).symm i))=P
    rw [Fintype.sum_equiv (registerFin (RowSlots.squares R)).symm _
      (fun i => supportUnits bob G R S.measurements P i i) (fun _ => rfl)]
    exact hu.total

private theorem coarse_two {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Op) (a b : ι) (hne : a≠b) :
    coarse B (fun c => decide (c=a ∨ c=b)) true=B a+B b := by
  unfold coarse
  have he (c : ι) : (if decide (c=a ∨ c=b)=true then B c else 0)=
      (if c=a then B a else 0)+(if c=b then B b else 0) := by
    by_cases hca : c=a
    · subst c; simp [hne]
    · by_cases hcb : c=b
      · subst c; simp [Ne.symm hne]
      · simp [hca,hcb]
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp

/-- The actual D_j, for either original support, is exactly E_00+E_jj. -/
theorem pair_D_diagonal (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) :
    pairJoint bob G R S.measurements P j 0+pairJoint bob G R S.measurements P j 1=
      numericalUnit bob G R S.measurements P 0 0+
        numericalUnit bob G R S.measurements P ⟨j,hj.2⟩ ⟨j,hj.2⟩ := by
  rw [pair_active_sector bob G R S hS h hm P hP j hj]
  let a0 := scalarAnswer G R 0
  let aj := scalarAnswer G R ⟨j,hj.2⟩
  have hne : a0≠aj := by intro he; have := congrArg Fin.val he; change 0=j at this; omega
  have he : (fun b : Answer G R => decide (b.val=0 ∨ b.val=j))=
      (fun b => decide (b=a0 ∨ b=aj)) := by
    funext b
    simp only [Fin.ext_iff,a0,aj,scalarAnswer,Fin.val_zero]
  rw [he,coarse_two _ a0 aj hne,globalZ_diagonal bob G R S hS h hm P hP,
    globalZ_diagonal bob G R S hS h hm P hP]
  rfl

/-- Literal 00 and jj blocks for the actual pair sum, with the original
    supported 00 corner as coefficient identity. -/
theorem pair_D_blocks (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    let e := numericalUnit bob G R S.measurements P 0 0
    matrixBlocks hu 0 (pairJoint bob G R S.measurements P j 0+pairJoint bob G R S.measurements P j 1)=
      Matrix.single 0 0 e+Matrix.single ⟨j,hj.2⟩ ⟨j,hj.2⟩ e := by
  dsimp only
  rw [pair_D_diagonal bob G R S hS h hm P hP j hj,MatrixBlocks.add,
    MatrixBlocks.unit,MatrixBlocks.unit]

#print axioms pure_new_fine_mirror
#print axioms globalZ_diagonal_bob
#print axioms globalZ_diagonal
#print axioms numericalUnit_laws
#print axioms coarse_two
#print axioms pair_D_diagonal
#print axioms pair_D_blocks
end Sigma2.RowScalar
