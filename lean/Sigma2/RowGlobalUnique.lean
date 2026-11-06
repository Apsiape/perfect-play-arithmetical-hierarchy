import Sigma2.RowScalarBindings

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral FiniteJoint

theorem dimension_bits {s} (R : Rows s) : RowSlots.dimension R=2^(2*RowSlots.squares R) := by
  change 4^RowSlots.squares R=_
  rw [pow_mul]
  norm_num

def bitAxis {s} (R : Rows s) (isX : Bool) (k : Fin (2*RowSlots.squares R)) : NewQ R :=
  axisQ R ⟨k.val/2,by have := k.isLt; omega⟩
    (globalAxis isX ⟨k.val%2,Nat.mod_lt _ (by decide)⟩)

/-- A measured scalar axis's positive or negative spectral projection. -/
def axisEffect (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (isX : Bool)
    (k : Fin (2*RowSlots.squares R)) (negative : Bool) : Op :=
  coarse (newEffects bob G R M P (bitAxis R isX k)) (fun a => decide (a.val=0)) negative

/-- The canonical joint spectral measure of the already certified scalar axes.
It contains no global-question effects. -/
def globalJoint (bob : Bool) (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (P : Op) (isX : Bool) (a : ℕ) : Op :=
  if a<RowSlots.dimension R then
    intersection P (fun k => axisEffect bob G R M P isX k (Nat.testBit a k.val))
      (List.finRange (2*RowSlots.squares R)) else 0

theorem global_bit_reject {s} (R : Rows s) (isX : Bool)
    (k : Fin (2*RowSlots.squares R)) (a b : ℕ)
    (hne : Nat.testBit a k.val≠decide (b=0)) :
    newRule R (.global isX) (bitAxis R isX k).val a b=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hd : directed R (.global isX) (bitAxis R isX k).val a b=true := by
    simp only [newRule,Bool.and_eq_true] at hh
    exact hh.1.2
  simp only [directed,List.all_eq_true] at hd
  have hj := hd ⟨k.val/2,by have := k.isLt; omega⟩ (List.mem_finRange _)
    ⟨k.val%2,Nat.mod_lt _ (by decide)⟩ (List.mem_finRange _)
  have hk : 2*(k.val/2)+k.val%2=k.val := by omega
  have he : b=bitAnswer (Nat.testBit a k.val) := by
    simpa only [bitAxis,axisQ_val,globalAxis,ite_true,decide_eq_true_eq,hk] using hj
  subst b
  apply hne
  cases Nat.testBit a k.val <;> simp [bitAnswer]

/-- Complete global fine-effect identification on either original support,
including every invalid padded answer. -/
theorem global_unique (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (isX : Bool) (a : Answer G R) :
    newEffects bob G R S.measurements P (globalQ R isX) a=
      globalJoint bob G R S.measurements P isX a.val := by
  let B := newEffects bob G R S.measurements P (globalQ R isX)
  let f := fun k : Fin (2*RowSlots.squares R) => fun a : Answer G R => Nat.testBit a.val k.val
  have hc (k : Fin (2*RowSlots.squares R)) (t : Bool) :=
    new_coarse_eq bob G R S hS h hm P hP (globalQ R isX) (bitAxis R isX k)
      (fun a => Nat.testBit a k.val) (fun b => decide (b=0))
      (global_bit_reject R isX k) t
  by_cases ha : a.val<RowSlots.dimension R
  · rw [globalJoint,if_pos ha]
    have he := fine_unique B P hP.1
      (new_positive bob G R S.measurements P hP.1 _) (new_sum bob G R S.measurements P hP.1 _)
      (fun b => b.val<RowSlots.dimension R)
      (fun b hb => new_invalid_zero bob G R S hS h hm P hP _ b (by simpa [globalQ,valid] using hb))
      f (List.finRange _) a (fun k => (hc k (f k a)).2) ha (by
        intro b hb heq
        apply Fin.ext
        apply RowParity.bounded_ext (n:=2*RowSlots.squares R) (by simpa only [← dimension_bits] using hb)
          (by simpa only [← dimension_bits] using ha)
        intro k hk
        exact heq ⟨k,hk⟩ (List.mem_finRange _))
    change B a=_
    rw [he]
    congr 1
    funext k
    exact (hc k (f k a)).1
  · rw [globalJoint,if_neg ha]
    exact new_invalid_zero bob G R S hS h hm P hP _ a (by simpa [globalQ,valid] using ha)

/-- Full uniqueness: any other POVM with the same sharp bit marginals and
zero invalid effects is the actual global POVM. -/
theorem global_competitor_unique (bob : Bool) (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : LocalMarginal bob S h) (P : Op) (hP : SupportOf h P)
    (isX : Bool) (B : Answer G R → Op) (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hz : ∀ a,RowSlots.dimension R≤a.val → B a=0)
    (hc : ∀ k t,coarse B (fun a => Nat.testBit a.val k.val) t=
      axisEffect bob G R S.measurements P isX k t) :
    ∀ a,B a=newEffects bob G R S.measurements P (globalQ R isX) a := by
  intro a
  rw [global_unique bob G R S hS h hm P hP]
  by_cases ha : a.val<RowSlots.dimension R
  · rw [globalJoint,if_pos ha]
    have hp (k : Fin (2*RowSlots.squares R)) :=
      (new_coarse_eq bob G R S hS h hm P hP (globalQ R isX) (bitAxis R isX k)
        (fun a => Nat.testBit a k.val) (fun b => decide (b=0))
        (global_bit_reject R isX k) (Nat.testBit a.val k.val))
    have he := fine_unique B P hP.1 hB hs (fun b => b.val<RowSlots.dimension R)
      (fun b hb => hz b (by omega)) (fun (k : Fin (2*RowSlots.squares R)) (a : Answer G R) => Nat.testBit a.val k.val) (List.finRange _) a
      (fun k => by rw [hc k]; change Projection (coarse (newEffects bob G R S.measurements P (bitAxis R isX k)) (fun a => decide (a.val=0)) (Nat.testBit a.val k.val)); rw [← (hp k).1]; exact (hp k).2) ha (by
        intro b hb heq
        apply Fin.ext
        apply RowParity.bounded_ext (n:=2*RowSlots.squares R) (by simpa only [← dimension_bits] using hb)
          (by simpa only [← dimension_bits] using ha)
        intro k hk
        exact heq ⟨k,hk⟩ (List.mem_finRange _))
    rw [he]
    congr 1
    funext k
    exact hc k (Nat.testBit a.val k.val)
  · rw [globalJoint,if_neg ha]; exact hz a (by omega)

#print axioms dimension_bits
#print axioms global_bit_reject
#print axioms global_unique
#print axioms global_competitor_unique
end Sigma2.RowScalar

