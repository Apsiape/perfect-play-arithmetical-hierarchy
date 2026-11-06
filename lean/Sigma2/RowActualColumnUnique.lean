import Sigma2.RowGraphEntries

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates RowColumns RowWalsh

/-- The existing graph uniqueness theorem at the exact numerical dimension. -/
theorem column_unique_of_graphs_dimension {d : ℕ} (n : ℕ) (hd : d=2^n)
    (V : Fin d → Op) (hV : ∀ j,Unitary (V j))
    (C : Fin d → Matrix (Fin d) (Fin d) Op) (A : Matrix (Fin d) (Fin d) Op)
    (hs : ∑ t,C t=A) (o : Fin d) (ho : o.val=0) (h0 : V o=1)
    (hz : ∀ t j,j≠o → C t*matrixGraph o j (V j) (!(parity n t.val j.val))=0) :
    ∀ t,C t=A*column n V t := by
  subst d
  exact column_unique_of_graphs n V hV C A hs o ho h0 hz

/-- Every actual column fine effect is the supported Walsh column of the
    actual signed slot reflections. This instantiates column_unique_of_graphs
    after transporting the actual graph effects and removing zero padding. -/
theorem actual_column_unique (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) (a : Fin (RowSlots.dimension R)) :
    let hu := numericalUnit_laws bob G R S hS h hm P hP
    let e := numericalUnit bob G R S.measurements P 0 0
    matrixBlocks hu 0 (newEffects bob G R S.measurements P (columnQ R r) (scalarAnswer G R a))=
      Matrix.diagonal (fun _ => e)*column (2*RowSlots.squares R)
        (fun j : Fin (RowSlots.dimension R) => slotCornerUnitary bob G R S.measurements P r j.val) a := by
  dsimp only
  let hu := numericalUnit_laws bob G R S hS h hm P hP
  let e := numericalUnit bob G R S.measurements P 0 0
  let C := fun a : Fin (RowSlots.dimension R) =>
    matrixBlocks hu 0 (newEffects bob G R S.measurements P (columnQ R r) (scalarAnswer G R a))
  let E : Matrix (Fin (RowSlots.dimension R)) (Fin (RowSlots.dimension R)) Op := Matrix.diagonal (fun _ => e)
  let V := fun j : Fin (RowSlots.dimension R) => slotCornerUnitary bob G R S.measurements P r j.val
  have hs : ∑ a,C a=E := by
    dsimp only [C,E,e]
    rw [← MatrixBlocks.sum,← scalarAnswer_sum G R _ (column_actual_partition bob G R S hS h hm P hP r).2.2.2,
      new_sum bob G R S.measurements P hP.1 _,MatrixBlocks.support]
  have hCE (a : Fin (RowSlots.dimension R)) : C a*E=C a := by
    dsimp only [C,E,e]
    rw [← MatrixBlocks.support hu 0,← MatrixBlocks.mul _ _ _ _
      (new_fine_supported bob G R S.measurements P hP.1 _ _).2,
      (new_fine_supported bob G R S.measurements P hP.1 _ _).2]
  apply column_unique_of_graphs_dimension (2*RowSlots.squares R) (dimension_bits R) V
    (fun j => slotCornerUnitary_unitary bob G R S hS h hm P hP r j.val) C E hs 0 rfl
    (slotCornerUnitary_zero bob G R S hS h hm P hP r)
    (fun t j hj => ?_) a
  have hn : j.val≠0 := by
    intro h; exact hj (Fin.ext h)
  have hj' : 0<j.val ∧ j.val<RowSlots.dimension R := ⟨Nat.pos_of_ne_zero hn,j.isLt⟩
  have hz := actual_column_blocks_graph_zero bob G R S hS h hm P hP r (scalarAnswer G R t) j.val hj'
    (!(parity (2*RowSlots.squares R) t.val j.val)) (by
      change (!(parity (2*RowSlots.squares R) t.val j.val))≠parity (2*RowSlots.squares R) t.val j.val
      cases parity (2*RowSlots.squares R) t.val j.val <;> decide)
  dsimp only at hz
  rw [slot_graph_blocks bob G R S hS h hm P hP r j.val hj'] at hz
  change C t*(E*matrixGraph 0 j (V j) (!(parity (2*RowSlots.squares R) t.val j.val)))=0 at hz
  rw [← mul_assoc,hCE] at hz
  exact hz

/-- Finite matrix form of supported reference overlap. The conclusion is a
    corner sum and makes no assertion on the ambient complement. -/
theorem supported_column_reference_sum {d : ℕ} (hd : 0<d) (bits : ℕ) (e : Op)
    (V : Fin d → Op) (o : Fin d) (ho : o.val=0) (h0 : V o=1)
    (hstar : ∀ j,star (V j)=V j)
    (hz : (Matrix.diagonal (fun _ => e)*column bits V o)*
      Matrix.of (fun _ _ : Fin d => (1/(d:ℂ)) • e)=0) :
    (∑ j : Fin d,(e*V j)*e)=0 := by
  let c : ℂ := 1/(d:ℂ)
  have hentry := congrArg (fun M : Matrix (Fin d) (Fin d) Op => M o o) hz
  rw [Matrix.mul_apply] at hentry
  simp only [Matrix.of_apply,Matrix.diagonal_mul,column,ho,RowParity.parity_zero,sign,
    Bool.false_eq_true,ite_false,mul_one,h0,one_mul,hstar,Matrix.zero_apply] at hentry
  change (∑ j : Fin d,(e*(c • V j))*(c • e))=0 at hentry
  have hs (j : Fin d) : (e*(c • V j))*(c • e)=(c*c) • ((e*V j)*e) := by
    simp only [mul_smul_comm,smul_mul_assoc,smul_smul]
  simp_rw [hs] at hentry
  rw [← Finset.smul_sum] at hentry
  have hc : c*c≠0 := by
    have hd' : (d:ℂ)≠0 := by exact_mod_cast Nat.ne_of_gt hd
    exact mul_ne_zero (one_div_ne_zero hd') (one_div_ne_zero hd')
  exact (smul_eq_zero.mp hentry).resolve_left hc

/-- The actual reference rejection forces the sum of actual corner
    reflections to vanish, on either original marginal support. -/
theorem actual_corner_row_sum (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (r : Fin R.rowCount) :
    (∑ j : Fin (RowSlots.dimension R),slotReflection bob G R S.measurements P r j.val)*
      numericalUnit bob G R S.measurements P 0 0=0 := by
  let hu := numericalUnit_laws bob G R S hS h hm P hP
  let e := numericalUnit bob G R S.measurements P 0 0
  let V := fun j : Fin (RowSlots.dimension R) => slotCornerUnitary bob G R S.measurements P r j.val
  let Ref : Matrix (Fin (RowSlots.dimension R)) (Fin (RowSlots.dimension R)) Op :=
    fun _ _ => (1/(RowSlots.dimension R:ℂ)) • e
  have hr : matrixBlocks hu 0 (newEffects bob G R S.measurements P (globalQ R true) (scalarAnswer G R 0))=Ref := by
    apply Matrix.ext
    intro i j
    exact globalX_zero_blocks bob G R S hS h hm P hP i j
  have hz := actual_column_blocks_reference_zero bob G R S hS h hm P hP r
  dsimp only at hz
  change matrixBlocks hu 0 (newEffects bob G R S.measurements P (columnQ R r) (scalarAnswer G R 0))*
    matrixBlocks hu 0 (newEffects bob G R S.measurements P (globalQ R true) (scalarAnswer G R 0))=0 at hz
  rw [actual_column_unique bob G R S hS h hm P hP r 0,hr] at hz
  change (Matrix.diagonal (fun _ => e)*column (2*RowSlots.squares R) V 0)*Ref=0 at hz
  have hs := supported_column_reference_sum (RowSlots.dimension_pos R) (2*RowSlots.squares R) e V 0 rfl
    (slotCornerUnitary_zero bob G R S hS h hm P hP r)
    (fun j => slotCornerUnitary_selfadjoint bob G R S hS h hm P hP r j.val) hz
  have he : e*e=e := (hu.diagonal_projection 0).2
  have hj (j : Fin (RowSlots.dimension R)) : (e*V j)*e=slotReflection bob G R S.measurements P r j.val*e := by
    rw [slotCornerUnitary_corner bob G R S hS h hm P hP,mul_assoc,he]
  simp_rw [hj] at hs
  rw [← Finset.sum_mul] at hs
  exact hs

#print axioms column_unique_of_graphs_dimension
#print axioms actual_column_unique
#print axioms supported_column_reference_sum
#print axioms actual_corner_row_sum
end Sigma2.RowScalar