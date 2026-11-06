import Sigma2.CompilerApproxDictionaryIndex
import Sigma2.RowCompletenessComplete

set_option backward.isDefEq.respectTransparency.types true
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxRows
open Compiler CompilerScaffold CompilerEventLoss RowCompleteness TensorLifts FiniteAncilla

/-- Exactly RowsHold, with only the two row-equation quantifiers restricted. -/
def RowsHoldOn {s} (R : Rows s) (S : NormalStrategy s)
    (keep : Fin R.rowCount → Prop) : Prop :=
  ∃ hA hB : Density, MarginalA S hA ∧ MarginalB S hB ∧
    (∀ i k, 0 < S.weight k →
      S.measurements.left (R.event i).x (R.event i).a (S.vector k)=
      S.measurements.right (R.event i).y (R.event i).b (S.vector k)) ∧
    (∀ r, keep r → ((R.constant r:ℂ) • (1:Op)+∑ i, (R.coefficient r i:ℂ) •
      S.measurements.alice (R.event i).x (R.event i).a)*hA.op=0) ∧
    (∀ r, keep r → ((R.constant r:ℂ) • (1:Op)+∑ i, (R.coefficient r i:ℂ) •
      S.measurements.bob (R.event i).y (R.event i).b)*hB.op=0)

def StructuralRowsHold (P : Presentation) (S : NormalStrategy (preGame P).scenario) : Prop :=
  RowsHoldOn (rows P) S (fun r => ¬ applicationRow P r)

theorem rowsHold_restrict {s} (R : Rows s) (S : NormalStrategy s)
    (keep : Fin R.rowCount → Prop) (hR : RowsHold R S) : RowsHoldOn R S keep := by
  obtain ⟨hA,hB,hmA,hmB,hm,ha,hb⟩ := hR
  exact ⟨hA,hB,hmA,hmB,hm,fun r _ => ha r,fun r _ => hb r⟩

/-- Compression needs synchronization, and no row equation at all. -/
theorem compressed_named_on (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy G.scenario) (keep : Fin R.rowCount → Prop) (hR : RowsHoldOn R S keep) (hN : NamedBinaryProjections R S) :
    ∃ E F : Fin R.count → Op,
      (∀ i,Projection (E i)) ∧ (∀ i,Projection (F i)) ∧
      (∀ i k,0<S.weight k →
        left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k)) ∧
      (∀ i k,0<S.weight k →
        right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k)) ∧
      (∀ i k,0<S.weight k → left (E i) (S.vector k)=right (F i) (S.vector k)) := by
  obtain ⟨hA,hB,P,Q,hmA,hmB,hP,hQ,hproj,hsync⟩ := hN
  obtain ⟨_,_,_,_,hmir,_,_⟩ := hR
  let E := fun i => P*S.measurements.alice (R.event i).x (R.event i).a*P
  let F := fun i => Q*S.measurements.bob (R.event i).y (R.event i).b*Q
  have he (i k) (hk : 0<S.weight k) :
      left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k) := by
    rw [measurements_left]
    exact compressed_left P _ _ (normal_left_support S hA hmA P hP k hk) (hproj i).1.1
  have hf (i k) (hk : 0<S.weight k) :
      right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k) := by
    rw [measurements_right]
    exact compressed_right Q _ _ (normal_right_support S hB hmB Q hQ k hk) (hproj i).2.1
  refine ⟨E,F,fun i => (hproj i).1.2,fun i => (hproj i).2.2,he,hf,?_⟩
  intro i k hk
  rw [he i k hk,hf i k hk]
  exact hmir i k hk

theorem named_row_zero_on (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (keep : Fin R.rowCount → Prop) (hR : RowsHoldOn R S keep) (E : Fin R.count → Op)
    (hE : ∀ i k,0<S.weight k →
      left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (r : Fin R.rowCount) (hr : keep r) (k : ℕ) (hk : 0<S.weight k) :
    left ((R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) • E i) (S.vector k)=0 := by
  obtain ⟨hA,hB,hmA,hmB,hmir,hrowA,hrowB⟩ := hR
  have hz := normal_left_zero S hA hmA _ (hrowA r hr) k hk
  have he : left ((R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) • E i) (S.vector k)=
      left ((R.constant r:ℂ) • (1:Op)+∑ i,(R.coefficient r i:ℂ) •
        S.measurements.alice (R.event i).x (R.event i).a) (S.vector k) := by
    simp only [DiagonalIdentification.left_add,MagicRelations.left_smul,left_sum,left_one,
      add_apply,smul_apply,sum_apply,
      one_apply_eq_self]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [hE i k hk,measurements_left]
  exact he.trans hz

theorem finite_slot_sum_zero_on (G : Game) (R : Rows G.scenario) (S : NormalStrategy G.scenario)
    (keep : Fin R.rowCount → Prop) (hR : RowsHoldOn R S keep) (E : Fin R.count → Op)
    (hE : ∀ i k,0<S.weight k →
      left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k))
    (r : Fin R.rowCount) (hr : keep r) (k : ℕ) (hk : 0<S.weight k) :
    left (∑ j : Fin (RowSlots.dimension R),(RowSlots.slot R r j.val).eval E) (S.vector k)=0 := by
  rw [finite_slot_sum,MagicRelations.left_smul]
  change (2*(RowSlots.denominator (RowSlots.coefficients R r):ℂ)) • left _ (S.vector k)=0
  rw [named_row_zero_on G R S keep hR E hE r hr k hk,smul_zero]

end Sigma2.CompilerApproxRows
