import Sigma2.RowScalarAlgebra
import Sigma2.RowSynchronization

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame TensorLifts Preliminaries CoarseCells FiniteSpectral

/-- Every new question is synchronized by its actual diagonal test. -/
theorem new_synchronized (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (q : NewQ R) (a : AA (scenario G R)) :
    BinaryEventSynchronized S ⟨qa G R q,qb G R q,a,a⟩ := by
  intro u v huv
  have hne : u.val≠v.val := by
    intro he
    apply huv
    have huvEq : u=v := Fin.ext he
    exact huvEq ▸ Iff.rfl
  apply rejected_probability G R S hS
  change accepts G R _ _ _ _=false
  simp only [accepts,decode_qa,decode_qb,newRule,ite_true]
  simp [hne]

/-- Fine new effects, including global, pair, slot and column effects, reduce
and are projections on the actual original normal support. -/
theorem new_sharp (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (q : NewQ R) (a : AA (scenario G R)) :
    BinaryProjectionOn P (S.measurements.alice (qa G R q) a) ∧
      Centralizes h.op (S.measurements.alice (qa G R q) a) :=
  RowSynchronization.binary_alice S _ h hm P hP (new_synchronized G R S hS q a)

/-- The same concrete synchronization makes every new Bob effect sharp on
his own original support; it does not use Alice's support as a surrogate. -/
theorem new_sharp_bob (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (P : Op) (hP : SupportOf h P)
    (q : NewQ R) (a : BB (scenario G R)) :
    BinaryProjectionOn P (S.measurements.bob (qb G R q) a) ∧
      Centralizes h.op (S.measurements.bob (qb G R q) a) :=
  RowSynchronization.binary_bob S _ h hm P hP (new_synchronized G R S hS q a)

def globalQ {s} (R : Rows s) (isX : Bool) : NewQ R :=
  ⟨.global isX,by cases isX <;> simp [questions]⟩

def globalAxis (isX : Bool) (k : Fin 2) : Fin 4 :=
  ⟨k.val+if isX then 2 else 0,by split <;> omega⟩

def bitClass (g : ℕ) (k : Fin 2) (a : ℕ) : Fin 4 :=
  if Nat.testBit a (2*g+k.val) then 2 else 1

theorem global_reject {s} (R : Rows s) (isX : Bool)
    (g : Fin (RowSlots.squares R)) (k : Fin 2) (a b : ℕ)
    (hne : bitClass g.val k a≠binaryClass b) :
    newRule R (.global isX) (axis R g (globalAxis isX k)) a b=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hd : directed R (.global isX) (axis R g (globalAxis isX k)) a b=true := by
    simp only [newRule,Bool.and_eq_true] at hh
    exact hh.1.2
  simp only [directed,List.all_eq_true] at hd
  have hj := hd g (List.mem_finRange g) k (List.mem_finRange k)
  change (if axis R g (globalAxis isX k)=axis R g (globalAxis isX k) then
    decide (b=bitAnswer (Nat.testBit a (2*g.val+k.val))) else true)=true at hj
  simp only [ite_true,decide_eq_true_eq] at hj
  subst b
  apply hne
  cases hb : Nat.testBit a (2*g.val+k.val) <;> simp [bitClass,bitAnswer,binaryClass,hb]

theorem pure_global_marginal (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (isX : Bool) (g : Fin (RowSlots.squares R)) (k : Fin 2) :
    signed (compressed P (S.measurements.alice (qa G R (globalQ R isX))))
      (fun a => bitClass g.val k a.val)=
      binary G R S.measurements P (axisQ R g (globalAxis isX k)) := by
  apply bound_signed G R S hS h hm P hP
  intro a b hab
  simpa only [globalQ,axisQ_val] using global_reject R isX g k a b hab

/-- Each actual global bit marginal is the corresponding measured scalar
axis on the original mixed-state support. -/
theorem global_marginal (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (isX : Bool) (g : Fin (RowSlots.squares R)) (k : Fin 2) :
    signed (compressed P (S.measurements.alice (qa G R (globalQ R isX))))
      (fun a => bitClass g.val k a.val)=
      binary G R S.measurements P (axisQ R g (globalAxis isX k)) := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  have hh := pure_global_marginal G R T (pure_perfect_transfer G R S hS T hprob)
    h (hM h hm) P hP isX g k
  simpa only [binary,hA] using hh

private theorem pure_global_action (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (isX : Bool) (g : Fin (RowSlots.squares R)) (k : Fin 2) (a : AA (scenario G R)) :
    binary G R S.measurements P (axisQ R g (globalAxis isX k))*
      compressed P (S.measurements.alice (qa G R (globalQ R isX))) a=
        (if Nat.testBit a.val (2*g.val+k.val) then (-1:ℂ) else 1) •
          compressed P (S.measurements.alice (qa G R (globalQ R isX))) a := by
  rw [← pure_global_marginal G R S hS h hm P hP isX g k]
  have hp (t : Fin 4) := (bound_analysis G R S hS h hm P hP
    (globalQ R isX) (axisQ R g (globalAxis isX k)) (bitClass g.val k) binaryClass
    (fun u v huv => by simpa only [globalQ,axisQ_val] using global_reject R isX g k u v huv) t).2
  rw [signed_action _ _ P hP.1 (compressed_positive P hP.1 _ (S.measurements.alice_pos _))
    (compressed_sum P hP.1 _ (S.measurements.alice_sum _)) hp]
  cases hb : Nat.testBit a.val (2*g.val+k.val) <;> simp [bitClass,signValue,hb]

/-- The actual global fine effects have exactly the joint spectral action of
all certified Z (or X) axes, for arbitrary normal states. -/
theorem global_spectral_action (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (isX : Bool) (g : Fin (RowSlots.squares R)) (k : Fin 2) (a : AA (scenario G R)) :
    binary G R S.measurements P (axisQ R g (globalAxis isX k))*
      compressed P (S.measurements.alice (qa G R (globalQ R isX))) a=
        (if Nat.testBit a.val (2*g.val+k.val) then (-1:ℂ) else 1) •
          compressed P (S.measurements.alice (qa G R (globalQ R isX))) a := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  have hh := pure_global_action G R T (pure_perfect_transfer G R S hS T hprob)
    h (hM h hm) P hP isX g k a
  simpa only [binary,hA] using hh

#print axioms new_sharp_bob
#print axioms new_sharp
#print axioms global_marginal
#print axioms global_spectral_action
end Sigma2.RowScalar

