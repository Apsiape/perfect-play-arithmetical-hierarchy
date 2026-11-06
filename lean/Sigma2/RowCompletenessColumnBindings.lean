import Sigma2.RowCompletenessCosetBindings
import Sigma2.RowCompletenessGraphZero
import Sigma2.RowCompletenessReference

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns RowWalsh FiniteAncilla TensorLifts

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem binary_constantDiagonal (d : ℕ) (E : Op) (hE : Projection E) (b : Bool) :
    (Partition.binary (constantDiagonal (d:=d) E)
      (constantDiagonal_projection E hE).1 (constantDiagonal_projection E hE).2).effect b=
      constantDiagonal (binaryEffect E b) := by
  cases b
  · change 1-constantDiagonal E=constantDiagonal (1-E)
    exact Matrix.diagonal_sub (fun _ : Fin d => (1:Op)) (fun _ => E)
  · rfl

theorem slot_binary_formula (n j : ℕ) (hj : j<2^n) (E : Op) (hE : Projection E) (u : Bool) (c : Fin 3) :
    (slotPartition n j hj E hE).effect (u,c)=constantDiagonal (binaryEffect E u)*
      ((pairPartition n j hj).coarse pairClass).effect c := by
  change (Partition.binary _ _ _).effect u*_=_
  rw [binary_constantDiagonal (2^n) E hE u]

theorem slot_eval_event {s} (R : Rows s) (E : Fin R.count → Op) (r : Fin R.rowCount) (j : ℕ) :
    (RowSlots.slot R r j).eval E=sign (RowSlots.slot R r j).negative • ((2:ℂ) • slotEvent R E r j-1) := by
  rw [slot_eval_sign]
  congr 1
  unfold slotEvent
  cases (RowSlots.slot R r j).event
  · change (1:Op)=(2:ℂ) • (1:Op)-1
    module
  · rfl

theorem column_pair_realized_dimension (n d j : ℕ) [NeZero d] (hd : d=2^n)
    (hjD : j<d) (hj : j<2^n) (V : Fin d → Op) (hs : ∀ i,star (V i)=V i) (h0 : V 0=1)
    (P : Op) (neg : Bool) (he : V ⟨j,hjD⟩*P=sign neg • P) (t : Fin d) (b : Bool)
    (hne : Bool.xor b neg≠parity n t.val j) :
    matrixOp d (RowColumns.column n V t)*matrixOp (2^n) (constantDiagonal P*(pairPartition n j hj).effect (b,0))=0 := by
  subst d
  rw [← matrixOp_mul,column_pair_event_zero n j hj V hs h0 P neg he t b hne,matrixOp_zero]

theorem uniform_dimension (n d : ℕ) [NeZero d] (hd : d=2^n) :
    matrixOp (2^n) (uniformBlocks (2^n))=matrixOp d (uniformBlocks d) := by
  subst d
  rfl

theorem column_slot_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (j : ℕ) (hj : j<2^(bits R))
    (t : Fin (RowSlots.dimension R)) (u : Bool) (c : Fin 2)
    (hne : Bool.xor (decide (c.val=1)) (Bool.xor (!u) (RowSlots.slot R r j).negative)≠
      parity (bits R) t.val j) :
    columnEffect R E r t*(realizePartition (slotPartition (bits R) j hj (slotEvent R E r j)
      (slotEvent_projection R E hE r j))).effect (u,activeClass c)=0 := by
  have he := binary_reflection_eigen (slotEvent R E r j) (slotEvent_projection R E hE r j)
    (RowSlots.slot R r j).negative u
  change _*binaryEffect (slotEvent R E r j) u=_ at he
  rw [← slot_eval_event] at he
  have hs := fun i : Fin (RowSlots.dimension R) => slot_selfadjoint E hE (RowSlots.slot R r i.val)
  have h0 : (RowSlots.slot R r 0).eval E=1 := by rw [RowSlots.slot_zero]; rfl
  have hslot : (realizePartition (slotPartition (bits R) j hj (slotEvent R E r j)
      (slotEvent_projection R E hE r j))).effect (u,activeClass c)=
      matrixOp (2^(bits R)) (constantDiagonal (binaryEffect (slotEvent R E r j) u)*
        (pairPartition (bits R) j hj).effect (decide (c.val=1),0)) := by
    change matrixOp _ _=_
    rw [slot_binary_formula _ _ _ _ (slotEvent_projection R E hE r j),pair_sector_active]
  rw [hslot]
  exact column_pair_realized_dimension (bits R) (RowSlots.dimension R) j (RowScalar.dimension_bits R)
    (by simpa only [RowScalar.dimension_bits] using hj) hj _ hs h0 _ _ he t _ hne

theorem column_slot_binding_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (j : ℕ) (hj : j<2^(bits R))
    (a b : AA (scenario G R)) (ha : a.val<RowSlots.dimension R) (hb : b.val<6)
    (hc : b.val%3≠2)
    (hne : Bool.xor (decide (b.val%3=1)) (Bool.xor (decide (b.val/3=0)) (RowSlots.slot R r j).negative)≠
      parity (bits R) a.val j) :
    (newPartition G R E hE (.column r)).effect a*(newPartition G R E hE (.slot r j)).effect b=0 := by
  obtain ⟨u,c,hb⟩ := decode_slot_answer b.val hb
  have hmod : b.val%3=c.val := by have := c.isLt; omega
  have hdiv : b.val/3=bit u := by have := c.isLt; omega
  have hcu : c.val<2 := by have := c.isLt; omega
  let c' : Fin 2 := ⟨c.val,hcu⟩
  have hcc : c=activeClass c' := Fin.ext rfl
  rw [column_effect G R E hE r ⟨a.val,ha⟩ a rfl,slot_effect G R E hE r j hj (u,c) b hb,hcc]
  apply column_slot_zero G R E hE r j hj ⟨a.val,ha⟩ u c'
  have hnot : decide (bit u=0)= !u := by cases u <;> rfl
  simpa only [hmod,hdiv,hnot] using hne

theorem fourier_zero_uniform (n : ℕ) : (fourierPartition n).effect 0=uniformBlocks (2^n) := by
  apply Matrix.ext
  intro i j
  simp only [fourierPartition,RowColumns.column,Fin.val_zero,RowParity.parity_zero,sign,
    Bool.false_eq_true,ite_false,mul_one,star_one,uniformBlocks]

theorem column_reference_binding_zero (G : Game) (R : Rows G.scenario) (E F : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (r : Fin R.rowCount) (v : AB)
    (hz : left (∑ j : Fin (RowSlots.dimension R),(RowSlots.slot R r j.val).eval E) v=0)
    (a b : AA (scenario G R)) (ha : a.val=0) (hb : b.val=0) :
    (left ((newPartition G R E hE (.column r)).effect a)*
      right ((newPartition G R F hF (.global true)).effect b)) (entangle (RowSlots.dimension R) v)=0 := by
  rw [column_effect G R E hE r 0 a ha,globalX_effect G R F hF 0 b hb]
  change (left (columnEffect R E r 0)*right (matrixOp _ _)) _=0
  rw [fourier_zero_uniform]
  rw [uniform_dimension (bits R) (RowSlots.dimension R) (RowScalar.dimension_bits R)]
  exact column_reference_zero R E hE r v hz

end Sigma2.RowCompleteness
