import Sigma2.RowCompletenessScalarBindings

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns RowWalsh FiniteAncilla

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem coset_parity (n j ell : ℕ) (hj : j<2^n) (t : Fin (2^n))
    (hp : parity n ell j=false) :
    parity n ell (cosetLabel n j hj t).val=parity n ell t.val := by
  unfold cosetLabel
  split_ifs
  · rfl
  · change parity n ell (Nat.xor t.val j)=_
    rw [RowScalar.parity_right_xor,hp,Bool.xor_false]

theorem pair_diagonal_zero (n j ell : ℕ) (hj : j<2^n) (b : Bool) (r t : Fin (2^n))
    (hp : parity n ell j=false) (hne : parity n ell r.val≠parity n ell t.val) :
    (realizePartition (pairPartition n j hj)).effect (b,r)*
      (realizePartition (diagonalPartition (2^n))).effect t=0 := by
  have hlabel : cosetLabel n j hj t≠r := by
    intro he
    apply hne
    rw [← he,coset_parity n j ell hj t hp]
  have he := (diagonalPartition (2^n)).coarse_action (cosetLabel n j hj) t r
  rw [if_neg hlabel] at he
  have hs := congrArg star he
  simp only [star_mul,(diagonalPartition (2^n)).selfadjoint,
    ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).selfadjoint,star_zero] at hs
  change matrixOp _ _*matrixOp _ _=0
  rw [← matrixOp_mul]
  change matrixOp _ (((Partition.reflection _ _ _).effect b*
    ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect r)*
      (diagonalPartition (2^n)).effect t)=0
  rw [mul_assoc,hs,mul_zero,matrixOp_zero]

theorem pair_Z_binding_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (j ell : ℕ) (hj : j<2^(bits R))
    (a b : AA (scenario G R)) (ha : a.val<2*RowSlots.dimension R) (hb : b.val<RowSlots.dimension R)
    (hp : parity (bits R) ell j=false)
    (hne : parity (bits R) ell (a.val/2)≠parity (bits R) ell b.val) :
    (newPartition G R E hE (.pair j)).effect a*(newPartition G R E hE (.global false)).effect b=0 := by
  have har : a.val<2*2^(bits R) := by simpa only [RowScalar.dimension_bits] using ha
  have hbr : b.val<2^(bits R) := by simpa only [RowScalar.dimension_bits] using hb
  obtain ⟨neg,r,ha⟩ := decode_pair_answer (bits R) a.val har
  rw [pair_effect G R E hE j hj (neg,r) a ha,globalZ_effect G R E hE ⟨b.val,hbr⟩ b rfl]
  apply pair_diagonal_zero (bits R) j ell hj neg r ⟨b.val,hbr⟩ hp
  have hdiv : a.val/2=r.val := by have := bit_lt neg; omega
  simpa only [hdiv] using hne

theorem decode_slot_answer (v : ℕ) (hv : v<6) : ∃ b : Bool,∃ c : Fin 3,v=3*bit b+c.val := by
  interval_cases v
  · exact ⟨false,0,rfl⟩
  · exact ⟨false,1,rfl⟩
  · exact ⟨false,2,rfl⟩
  · exact ⟨true,0,rfl⟩
  · exact ⟨true,1,rfl⟩
  · exact ⟨true,2,rfl⟩

theorem scalarClass_encoded {n : ℕ} (b : Bool) (r : Fin (2^n)) :
    scalarClass (2*r.val+bit b)=(pairClass (b,r)).val := by
  have hb := bit_lt b
  have hd : (2*r.val+bit b)/2=r.val := by omega
  have hm : (2*r.val+bit b)%2=bit b := by omega
  simp only [scalarClass,hd,hm,pairClass]
  by_cases hr : r.val=0
  · simp only [hr,ite_true]
    cases b <;> rfl
  · simp only [hr,ite_false]
    rfl

theorem slot_pair_zero (n j : ℕ) (hj : j<2^n) (E : Op) (hE : Projection E)
    (u : Bool) (c : Fin 3) (neg : Bool) (r : Fin (2^n)) (hne : c≠pairClass (neg,r)) :
    (realizePartition (slotPartition n j hj E hE)).effect (u,c)*
      (realizePartition (pairPartition n j hj)).effect (neg,r)=0 := by
  have he := (pairPartition n j hj).coarse_action pairClass (neg,r) c
  rw [if_neg (Ne.symm hne)] at he
  have hs := congrArg star he
  simp only [star_mul,(pairPartition n j hj).selfadjoint,
    ((pairPartition n j hj).coarse pairClass).selfadjoint,star_zero] at hs
  change matrixOp _ _*matrixOp _ _=0
  rw [← matrixOp_mul]
  change matrixOp _ (((Partition.binary _ _ _).effect u*
    ((pairPartition n j hj).coarse pairClass).effect c)*(pairPartition n j hj).effect (neg,r))=0
  rw [mul_assoc,hs,mul_zero,matrixOp_zero]

theorem slot_pair_binding_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (j : ℕ) (hj : j<2^(bits R))
    (a b : AA (scenario G R)) (ha : a.val<6) (hb : b.val<2*RowSlots.dimension R)
    (hne : a.val%3≠scalarClass b.val) :
    (newPartition G R E hE (.slot r j)).effect a*(newPartition G R E hE (.pair j)).effect b=0 := by
  obtain ⟨u,c,ha⟩ := decode_slot_answer a.val ha
  have hbr : b.val<2*2^(bits R) := by simpa only [RowScalar.dimension_bits] using hb
  obtain ⟨neg,t,hb⟩ := decode_pair_answer (bits R) b.val hbr
  rw [slot_effect G R E hE r j hj (u,c) a ha,pair_effect G R E hE j hj (neg,t) b hb]
  apply slot_pair_zero
  intro he
  apply hne
  have hm : a.val%3=c.val := by have := c.isLt; omega
  rw [hm,hb,scalarClass_encoded,he]

theorem slot_one_false_zero (n j : ℕ) (hj : j<2^n) (hI : Projection (1:Op)) (c : Fin 3) :
    (realizePartition (slotPartition n j hj 1 hI)).effect (false,c)=0 := by
  change matrixOp _ ((1-constantDiagonal 1)*_)=0
  have he : constantDiagonal (d:=2^n) (1:Op)=1 := Matrix.diagonal_one
  rw [he,sub_self,zero_mul,matrixOp_zero]

theorem slot_anchor_binding_zero (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (j : ℕ) (hj : j<2^(bits R))
    (he : (RowSlots.slot R r j).event=none) (a : AA (scenario G R)) (ha : a.val<6)
    (hne : a.val/3≠1) : (newPartition G R E hE (.slot r j)).effect a=0 := by
  obtain ⟨u,c,ha⟩ := decode_slot_answer a.val ha
  rw [slot_effect G R E hE r j hj (u,c) a ha]
  have hu : u=false := by cases u <;> simp_all [bit]
  subst u
  have hslot : slotEvent R E r j=1 := by simp only [slotEvent,he]
  simp only [hslot]
  exact slot_one_false_zero _ _ _ _ c

end Sigma2.RowCompleteness
