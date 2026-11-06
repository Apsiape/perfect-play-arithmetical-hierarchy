import Sigma2.RowSlotExtraction

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral MatrixSupportCoordinates

/-- Every event in a slot is the actual old named projection or the anchor P,
on the chosen original normal support. -/
theorem slotEvent_laws (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) :
    Projection (slotEvent bob G R S.measurements P r j) ∧
      P*slotEvent bob G R S.measurements P r j=slotEvent bob G R S.measurements P r j ∧
      slotEvent bob G R S.measurements P r j*P=slotEvent bob G R S.measurements P r j := by
  cases he : (RowSlots.slot R r j).event with
  | none => simpa only [slotEvent,he] using ⟨hP.1,hP.1.2,hP.1.2⟩
  | some i =>
    simp only [slotEvent,he]
    cases bob
    · exact ⟨old_projection G R S hS h hm P hP i,
        by simp only [localOld,Bool.false_eq_true,ite_false,oldEffect,← mul_assoc,hP.1.2],
        by simp only [localOld,Bool.false_eq_true,ite_false,oldEffect,mul_assoc,hP.1.2]⟩
    · exact ⟨old_bob_projection G R S hS h hm P hP i,
        by simp only [localOld,ite_true,oldBobEffect,← mul_assoc,hP.1.2],
        by simp only [localOld,ite_true,oldBobEffect,mul_assoc,hP.1.2]⟩

theorem slotEvent_commute (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (k l : Register (RowSlots.squares R)) :
    Commute (slotEvent bob G R S.measurements P r j)
      (supportUnits bob G R S.measurements P k l) := by
  cases he : (RowSlots.slot R r j).event with
  | none =>
    simp only [slotEvent,he]
    have hu := supportUnits_laws bob G R S hS h hm P hP
    exact (hu.supported k l).1.trans (hu.supported k l).2.symm
  | some i =>
    simp only [slotEvent,he]
    cases bob
    · exact old_units_commute G R S hS h hm P hP i k l
    · exact old_bob_units_commute G R S hS h hm P hP i k l

/-- The graph coefficient is a genuine signed reflection in the same scalar
commutant, including both anchor signs. -/
theorem slotReflection_laws (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) :
    star (slotReflection bob G R S.measurements P r j)=slotReflection bob G R S.measurements P r j ∧
      slotReflection bob G R S.measurements P r j*slotReflection bob G R S.measurements P r j=P := by
  let E := slotEvent bob G R S.measurements P r j
  have he := slotEvent_laws bob G R S hS h hm P hP r j
  change Projection E ∧ P*E=E ∧ E*P=E at he
  have hstar : star ((2:ℂ) • E-P)=(2:ℂ) • E-P := by
    have ht := star_sub ((2:ℂ) • E) P
    have hc := star_smul (2:ℂ) E
    rw [ht,hc,he.1.1,hP.1.1,star_ofNat]
  have hsquare : ((2:ℂ) • E-P)*((2:ℂ) • E-P)=P := by
    simp only [sub_mul,mul_sub,smul_mul_smul_comm,smul_mul_assoc,mul_smul_comm]
    rw [he.1.2,he.2.1,he.2.2,hP.1.2]
    module
  constructor
  · simp only [slotReflection,star_smul,RowColumns.sign_star]
    exact congrArg (fun A : Op => RowColumns.sign (RowSlots.slot R r j).negative • A) hstar
  · rw [slotReflection,smul_mul_smul_comm,RowColumns.sign_sq,one_smul]
    exact hsquare

theorem slotReflection_anchor (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (r : Fin R.rowCount) (j : ℕ)
    (he : (RowSlots.slot R r j).event=none) :
    slotReflection bob G R M P r j=RowColumns.sign (RowSlots.slot R r j).negative • P := by
  simp only [slotReflection,slotEvent,he]
  congr 1
  module

/-- Orthogonal active graph partition of exactly the {0,j} scalar sector. -/
theorem slot_graph_partition (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (j : ℕ) (hj : 0<j ∧ j<RowSlots.dimension R) :
    slotGraph bob G R S.measurements P r j hj false+
        slotGraph bob G R S.measurements P r j hj true=
      coarse (newEffects bob G R S.measurements P (globalQ R false))
        (fun b => decide (b.val=0 ∨ b.val=j)) true ∧
    slotGraph bob G R S.measurements P r j hj false*
      slotGraph bob G R S.measurements P r j hj true=0 := by
  constructor
  · rw [slot_graph_formula bob G R S hS h hm P hP r j hj false,
      slot_graph_formula bob G R S hS h hm P hP r j hj true,
      ← pair_active_sector bob G R S hS h hm P hP j hj]
    norm_num only [RowColumns.sign,Bool.false_eq_true,ite_false,ite_true,one_smul,neg_one_smul]
    module
  · rw [← slot_graph_coarse bob G R S hS h hm P hP r j hj false,
      ← slot_graph_coarse bob G R S hS h hm P hP r j hj true]
    let B := newEffects bob G R S.measurements P (slotQ R r j hj)
    change coarse B (fun a => slotGraphLabel R r j false a.val) true *
      (∑ a,if slotGraphLabel R r j true a.val=true then B a else 0)=0
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ht : slotGraphLabel R r j true a.val=true
    · rw [if_pos ht,coarse_action B (fun a => slotGraphLabel R r j false a.val) true
        P hP.1 (new_positive bob G R S.measurements P hP.1 _)
        (new_sum bob G R S.measurements P hP.1 _)
        (new_coarse_sharp bob G R S hS h hm P hP _ _ true)]
      have hf : slotGraphLabel R r j false a.val≠true := by
        simp only [slotGraphLabel,decide_eq_true_eq] at ht ⊢
        intro hh
        simp only [decide_eq_true_eq] at hh
        have he := hh.2.symm.trans ht.2
        exact Bool.noConfusion he
      rw [if_neg hf]
    · rw [if_neg ht,mul_zero]

/-- From perfection alone, all actual signed slot graphs on both original
supports, with their canonical spectral formulas, are available simultaneously. -/
theorem slot_graph_two_sided (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S) :
    ∃ (hA hB : Density) (P Q : Op),
      MarginalA S hA ∧ MarginalB S hB ∧ SupportOf hA P ∧ SupportOf hB Q ∧
      (∀ r j hj eps,Projection (slotGraph false G R S.measurements P r j hj eps) ∧
        slotGraph false G R S.measurements P r j hj eps=
          (1/2:ℂ) • ((pairJoint false G R S.measurements P j 0+pairJoint false G R S.measurements P j 1)+
            RowColumns.sign eps • (slotReflection false G R S.measurements P r j*
              (pairJoint false G R S.measurements P j 0-pairJoint false G R S.measurements P j 1)))) ∧
      (∀ r j hj eps,Projection (slotGraph true G R S.measurements Q r j hj eps) ∧
        slotGraph true G R S.measurements Q r j hj eps=
          (1/2:ℂ) • ((pairJoint true G R S.measurements Q j 0+pairJoint true G R S.measurements Q j 1)+
            RowColumns.sign eps • (slotReflection true G R S.measurements Q r j*
              (pairJoint true G R S.measurements Q j 0-pairJoint true G R S.measurements Q j 1)))) := by
  obtain ⟨hA,hB,hmA,hmB⟩ := marginals_exist S
  obtain ⟨P,hP⟩ := support_exists hA
  obtain ⟨Q,hQ⟩ := support_exists hB
  exact ⟨hA,hB,P,Q,hmA,hmB,hP,hQ,
    fun r j hj eps => ⟨slot_graph_projection false G R S hS hA hmA P hP r j hj eps,
      slot_graph_formula false G R S hS hA hmA P hP r j hj eps⟩,
    fun r j hj eps => ⟨slot_graph_projection true G R S hS hB hmB Q hQ r j hj eps,
      slot_graph_formula true G R S hS hB hmB Q hQ r j hj eps⟩⟩

#print axioms slotEvent_laws
#print axioms slotEvent_commute
#print axioms slotReflection_laws
#print axioms slotReflection_anchor
#print axioms slot_graph_partition
#print axioms slot_graph_two_sided
end Sigma2.RowScalar

