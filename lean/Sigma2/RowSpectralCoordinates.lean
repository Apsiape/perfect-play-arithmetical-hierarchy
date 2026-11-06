import Sigma2.RowPairCosets

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral FiniteJoint MatrixSupportCoordinates

private theorem binary_coarse_formula {ι : Type} [Fintype ι]
    (B : ι → Op) (num : ι → ℕ) (P : Op) (hs : ∑ a,B a=P)
    (hz : ∀ a,2≤num a → B a=0) (negative : Bool) :
    coarse B (fun a => decide (num a=0)) negative=
      (1/2:ℂ) • (P+(if negative then (-1:ℂ) else 1) • signed B (fun a => binaryClass (num a))) := by
  let p := fun a : ι => decide (num a=0)
  have hsum : coarse B p false+coarse B p true=P := by
    have hh := (coarse_sum B p).trans hs
    simpa [Fintype.sum_bool,add_comm] using hh
  have hdiff : signed B (fun a => binaryClass (num a))=coarse B p false-coarse B p true := by
    unfold signed coarse
    rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : num a<2
    · have he : num a=0 ∨ num a=1 := by omega
      rcases he with he | he <;> simp [p,binaryClass,he]
    · rw [hz a (by omega)]
      simp
  rw [hdiff,← hsum]
  cases negative <;> simp only [Bool.false_eq_true,Bool.true_eq,ite_false,ite_true,one_smul,neg_one_smul] <;> module

/-- The scalar bit factors in globalJoint are exactly the certified Pauli
spectral projections (P ± sigma)/2, on either actual support. -/
theorem axis_effect_formula (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (isX : Bool) (k : Fin (2*RowSlots.squares R)) (negative : Bool) :
    axisEffect bob G R S.measurements P isX k negative=
      (1/2:ℂ) • (P+(if negative then (-1:ℂ) else 1) •
        (if bob then bobBinary G R S.measurements P (bitAxis R isX k)
          else binary G R S.measurements P (bitAxis R isX k))) := by
  have hz (a : Answer G R) (ha : 2≤a.val) :
      newEffects bob G R S.measurements P (bitAxis R isX k) a=0 := by
    apply new_invalid_zero bob G R S hS h hm P hP
    unfold bitAxis axisQ
    split_ifs <;> simp [cellQ,valid,show ¬a.val<2 by omega]
  have hh := binary_coarse_formula (newEffects bob G R S.measurements P (bitAxis R isX k))
    Fin.val P (new_sum bob G R S.measurements P hP.1 _) hz negative
  cases bob
  · change coarse (compressed P (S.measurements.alice (qa G R (bitAxis R isX k))))
        (fun a => decide (a.val=0)) negative=_ at hh ⊢
    exact hh
  · change coarse (compressed P (S.measurements.bob (qb G R (bitAxis R isX k))))
        (fun a => decide (a.val=0)) negative=_ at hh ⊢
    exact hh

/-- Coordinates of any supported operator in precisely step 1's common units.
No independent basis or replacement effect is chosen. -/
def coordinateAction {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : Op} {t : ι → ι → Op} (_hu : Units P t) (o : ι) (A : Op)
    (w : PiLp 2 (fun _ : ι => space (t o o))) (i : ι) : H :=
  t o i (A (∑ j,t j o (w j)))

theorem coordinateAction_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : Op} {t : ι → ι → Op} (hu : Units P t) (o : ι) (A : Op)
    (hA : P*A=A) (w : PiLp 2 (fun _ : ι => space (t o o))) (i : ι) :
    let v : space P := ⟨A ((hu.coordinates o).symm w),by
      rw [mem_space]; exact congrArg (fun B : Op => B ((hu.coordinates o).symm w)) hA⟩
    ((hu.coordinates o v) i:H)=coordinateAction hu o A w i := by
  rfl

/-- Global-coordinate identification for any supplied actual common-unit
system, in particular the Alice and transposed/reversed Bob systems of step 1. -/
theorem global_coordinates (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    {ι : Type} [Fintype ι] [DecidableEq ι] {t : ι → ι → Op} (hu : Units P t)
    (o : ι) (isX : Bool) (a : Answer G R) :
    coordinateAction hu o (newEffects bob G R S.measurements P (globalQ R isX) a)=
      coordinateAction hu o (globalJoint bob G R S.measurements P isX a.val) := by
  rw [global_unique bob G R S hS h hm P hP]

/-- Complete pair-coordinate identification in the same actual common units. -/
theorem pair_coordinates (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    {ι : Type} [Fintype ι] [DecidableEq ι] {t : ι → ι → Op} (hu : Units P t)
    (o : ι) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) (a : Answer G R) :
    coordinateAction hu o (newEffects bob G R S.measurements P (pairQ R j hj) a)=
      coordinateAction hu o (pairJoint bob G R S.measurements P j a.val) := by
  rw [pair_unique bob G R S hS h hm P hP]


/-- The actual Alice or reversed-word Bob scalar units already constructed in
step 1; the choice never changes the strategy or its original support. -/
def supportUnits (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) :
    Register (RowSlots.squares R) → Register (RowSlots.squares R) → Op :=
  if bob then bobTensor G R M P else tensorUnit P (localUnit G R M P)

theorem supportUnits_laws (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P) :
    Units P (supportUnits bob G R S.measurements P) := by
  cases bob
  · have hh := common_matrix_units G R S hS h hm P hP
    exact ⟨hh.1,hh.2.1,hh.2.2⟩
  · have hh := bob_matrix_units G R S hS h hm P hP
    exact ⟨hh.1,hh.2.1,hh.2.2⟩

/-- Step 2 in precisely step 1's coordinates, on either original marginal
support, with every global and every canonical pair fine answer identified. -/
theorem support_global_pair_coordinates (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P) :
    let hu := supportUnits_laws bob G R S hS h hm P hP
    let o := zeroRegister (RowSlots.squares R)
    (∀ isX a,coordinateAction hu o (newEffects bob G R S.measurements P (globalQ R isX) a)=
      coordinateAction hu o (globalJoint bob G R S.measurements P isX a.val)) ∧
    (∀ j hj a,coordinateAction hu o (newEffects bob G R S.measurements P (pairQ R j hj) a)=
      coordinateAction hu o (pairJoint bob G R S.measurements P j a.val)) := by
  exact ⟨fun isX a => global_coordinates bob G R S hS h hm P hP _ _ isX a,
    fun j hj a => pair_coordinates bob G R S hS h hm P hP _ _ j hj a⟩

/-- Perfection alone supplies both original supports and all complete spectral
identifications. No decomposition, parity-syndrome assertion, or paper theorem
is supplied as a caller hypothesis. -/
theorem global_pair_two_sided (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S) :
    ∃ (hA hB : Density) (P Q : Op),
      MarginalA S hA ∧ MarginalB S hB ∧ SupportOf hA P ∧ SupportOf hB Q ∧
      (∀ isX a,newEffects false G R S.measurements P (globalQ R isX) a=
        globalJoint false G R S.measurements P isX a.val) ∧
      (∀ isX a,newEffects true G R S.measurements Q (globalQ R isX) a=
        globalJoint true G R S.measurements Q isX a.val) ∧
      (∀ j hj a,newEffects false G R S.measurements P (pairQ R j hj) a=
        pairJoint false G R S.measurements P j a.val) ∧
      (∀ j hj a,newEffects true G R S.measurements Q (pairQ R j hj) a=
        pairJoint true G R S.measurements Q j a.val) := by
  obtain ⟨hA,hB,hmA,hmB⟩ := marginals_exist S
  obtain ⟨P,hP⟩ := support_exists hA
  obtain ⟨Q,hQ⟩ := support_exists hB
  exact ⟨hA,hB,P,Q,hmA,hmB,hP,hQ,
    global_unique false G R S hS hA hmA P hP,
    global_unique true G R S hS hB hmB Q hQ,
    pair_unique false G R S hS hA hmA P hP,
    pair_unique true G R S hS hB hmB Q hQ⟩


#print axioms binary_coarse_formula
#print axioms axis_effect_formula
#print axioms coordinateAction_eq
#print axioms global_coordinates
#print axioms pair_coordinates
#print axioms supportUnits_laws
#print axioms support_global_pair_coordinates
#print axioms global_pair_two_sided
end Sigma2.RowScalar



