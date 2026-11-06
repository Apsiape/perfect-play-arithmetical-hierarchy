import Sigma2.RowColumnRejections

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral FiniteJoint

/-- The range-complement projection corresponding to one forbidden active graph. -/
def columnAllowedFactor (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (r : Fin R.rowCount)
    (a : Answer G R) (j : Fin (RowSlots.dimension R)) : Op :=
  if hj : 0<j.val then P-slotGraph bob G R M P r j.val ⟨hj,j.isLt⟩
    (!(parity (2*RowSlots.squares R) a.val j.val)) else P

theorem column_allowed_factor_projection (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a : Answer G R) (j : Fin (RowSlots.dimension R)) :
    Projection (columnAllowedFactor bob G R S.measurements P r a j) := by
  unfold columnAllowedFactor
  split_ifs with hj
  · let eps := !(parity (2*RowSlots.squares R) a.val j.val)
    let B := slotGraph bob G R S.measurements P r j.val ⟨hj,j.isLt⟩ eps
    have hb := slot_graph_projection bob G R S hS h hm P hP r j.val ⟨hj,j.isLt⟩ eps
    have hs : P*B=B ∧ B*P=B := by
      dsimp [B]
      rw [← slot_graph_coarse bob G R S hS h hm P hP]
      exact new_coarse_supported bob G R S.measurements P hP.1 _ _ true
    change Projection (P-B)
    constructor
    · exact (star_sub P B).trans (congrArg₂ (fun X Y : Op => X-Y) hP.1.1 hb.1)
    · rw [sub_mul,mul_sub,mul_sub,hP.1.2,hs.1,hs.2,hb.2]
      abel
  · exact hP.1

/-- Actual operator containment from the forbidden pairs, in both multiplication
orders. It includes every column answer and every signed anchor slot. -/
theorem column_allowed_factor (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a : Answer G R) (j : Fin (RowSlots.dimension R)) :
    let C := newEffects bob G R S.measurements P (columnQ R r) a
    C*columnAllowedFactor bob G R S.measurements P r a j=C ∧
      columnAllowedFactor bob G R S.measurements P r a j*C=C := by
  dsimp only
  have hc := new_fine_supported bob G R S.measurements P hP.1 (columnQ R r) a
  unfold columnAllowedFactor
  split_ifs with hj
  · have hne : (!(parity (2*RowSlots.squares R) a.val j.val))≠
        parity (2*RowSlots.squares R) a.val j.val := by
      cases parity (2*RowSlots.squares R) a.val j.val <;> decide
    constructor
    · rw [mul_sub,hc.2,column_graph_zero bob G R S hS h hm P hP r a j.val ⟨hj,j.isLt⟩ _ hne,sub_zero]
    · rw [sub_mul,hc.1,graph_column_zero bob G R S hS h hm P hP r a j.val ⟨hj,j.isLt⟩ _ hne,sub_zero]
  · exact ⟨hc.2,hc.1⟩

/-- The actual column effect is supported in the complete ordered intersection
of the allowed graph complements. The factors need not commute. -/
theorem column_allowed_intersection (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a : Answer G R) (ks : List (Fin (RowSlots.dimension R))) :
    let C := newEffects bob G R S.measurements P (columnQ R r) a
    let A := intersection P (columnAllowedFactor bob G R S.measurements P r a) ks
    C*A=C ∧ A*C=C := by
  dsimp only
  induction ks with
  | nil =>
    have hc := new_fine_supported bob G R S.measurements P hP.1 (columnQ R r) a
    exact ⟨hc.2,hc.1⟩
  | cons k ks ih =>
    have hk := column_allowed_factor bob G R S hS h hm P hP r a k
    constructor
    · rw [intersection,← mul_assoc,hk.1,ih.1]
    · rw [intersection,mul_assoc,ih.2,hk.2]

theorem new_fine_orthogonal (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (q : NewQ R) (a b : Answer G R) (hab : a≠b) :
    newEffects bob G R S.measurements P q a*newEffects bob G R S.measurements P q b=0 := by
  let B := newEffects bob G R S.measurements P q
  let f := fun c : Answer G R => decide (c.val=a.val)
  have he : coarse B f true=B a := by
    simp only [coarse,f,decide_eq_true_eq,← Fin.ext_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  have hh := coarse_action B f true P hP.1 (new_positive bob G R S.measurements P hP.1 q)
    (new_sum bob G R S.measurements P hP.1 q)
    (by rw [he]; exact new_fine_projection bob G R S hS h hm P hP q a) b
  have hf : f b≠true := by
    intro hfb
    change decide (b.val=a.val)=true at hfb
    have hv : b.val=a.val := of_decide_eq_true hfb
    exact hab (Fin.ext hv).symm
  rw [he,ite_eq_right hf] at hh
  exact hh

/-- The entire actual synchronized column measurement is a PVM on its
original support; every padded answer vanishes. -/
theorem column_actual_partition (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) :
    let C := newEffects bob G R S.measurements P (columnQ R r)
    (∑ a,C a)=P ∧ (∀ a,Projection (C a)) ∧
      (∀ a b,a≠b → C a*C b=0) ∧
      ∀ a,RowSlots.dimension R≤a.val → C a=0 := by
  dsimp only
  refine ⟨new_sum bob G R S.measurements P hP.1 _,
    fun a => new_fine_projection bob G R S hS h hm P hP _ a,
    fun a b hab => new_fine_orthogonal bob G R S hS h hm P hP _ a b hab,?_⟩
  intro a ha
  exact new_invalid_zero bob G R S hS h hm P hP _ a (by simp [columnQ,valid,show ¬a.val<RowSlots.dimension R by omega])

/-- The actual zero-column/reference identity in the previously certified
complete spectral normal form, without replacing the reference measurement. -/
theorem column_reference_spectral (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) :
    newEffects bob G R S.measurements P (columnQ R r) (zeroAnswer G R)*
      globalJoint bob G R S.measurements P true 0=0 := by
  have hh := column_reference_zero bob G R S hS h hm P hP r
  rw [global_unique bob G R S hS h hm P hP] at hh
  exact hh

#print axioms column_allowed_factor_projection
#print axioms column_allowed_factor
#print axioms column_allowed_intersection
#print axioms new_fine_orthogonal
#print axioms column_actual_partition
#print axioms column_reference_spectral
end Sigma2.RowScalar
