import Sigma2.CoarseCells
import Sigma2.PureTransfer

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowSynchronization
open Compiler Preliminaries TensorLifts PureTransfer

/-- Zero disagreement for the binary coarse outcomes gives the actual mirror,
sharp compression, and centralizer equation. The other questions are arbitrary. -/
theorem pure_binary_analysis {s} (S : PureStrategy s) (e : NamedEvent s)
    (h : Density) (hm : MarginalA (normalOfPure S) h)
    (P : Op) (hP : SupportOf h P)
    (hs : BinaryEventSynchronized (normalOfPure S) e) :
    S.measurements.left e.x e.a S.vector=S.measurements.right e.y e.b S.vector ∧
    BinaryProjectionOn P (S.measurements.alice e.x e.a) ∧
    Centralizes h.op (S.measurements.alice e.x e.a) := by
  have hz (a b) (hne : ¬ (a=e.a ↔ b=e.b)) :
      (inner ℂ S.vector ((left (S.measurements.alice e.x a)*
        right (S.measurements.bob e.y b)) S.vector)).re=0 := by
    have hh := hs a b hne
    rw [normalOfPure_probability] at hh
    change (inner ℂ S.vector ((S.measurements.left e.x a*
      S.measurements.right e.y b) S.vector)).re=0 at hh
    rwa [measurements_left,measurements_right] at hh
  have hh := CoarseCells.finite_matching_analysis S h hm P hP
    (S.measurements.alice e.x) (S.measurements.bob e.y)
    (S.measurements.alice_pos e.x) (S.measurements.bob_pos e.y)
    (S.measurements.alice_sum e.x) (S.measurements.bob_sum e.y) e.a e.b
    (fun b hb => hz e.a b (by simpa using hb))
    (fun a ha => hz a e.b (by simpa using ha))
  refine ⟨?_,hh.2,?_⟩
  · simpa only [measurements_left,measurements_right] using hh.1
  · exact MirrorCentralizer.mirrors_centralize S h hm _ _
      (S.measurements.alice_pos _ _) (S.measurements.bob_pos _ _) hh.1

/-- Purification preserves Alice's supplied marginal and operators. -/
theorem binary_alice {s} (S : NormalStrategy s) (e : NamedEvent s)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (hs : BinaryEventSynchronized S e) :
    BinaryProjectionOn P (S.measurements.alice e.x e.a) ∧
    Centralizes h.op (S.measurements.alice e.x e.a) := by
  obtain ⟨T,hA,_,hM,hprob⟩ := preserving_alice S
  have hT : BinaryEventSynchronized (normalOfPure T) e := by
    intro a b hab
    rw [normalOfPure_probability,← hprob]
    exact hs a b hab
  have hh := (pure_binary_analysis T e h (hM h hm) P hP hT).2
  simpa only [hA] using hh

/-- The same argument on Bob's actual support, through the checked swap. -/
theorem binary_bob {s} (S : NormalStrategy s) (e : NamedEvent s)
    (h : Density) (hm : MarginalB S h) (P : Op) (hP : SupportOf h P)
    (hs : BinaryEventSynchronized S e) :
    BinaryProjectionOn P (S.measurements.bob e.y e.b) ∧
    Centralizes h.op (S.measurements.bob e.y e.b) := by
  let ef : NamedEvent (flipScenario s) := ⟨e.y,e.x,e.b,e.a⟩
  have hf : BinaryEventSynchronized (flipNormal S) ef := by
    intro b a hab
    exact (flipNormal_probability S e.x e.y a b).trans
      (hs a b (fun hh => hab hh.symm))
  exact binary_alice (flipNormal S) ef h hm P hP hf

/-- The paper's support-projection premise follows from the existing binary
synchronization tests, for every finite family on one shared normal strategy. -/
theorem named_of_synchronized {s} (R : Rows s) (S : NormalStrategy s)
    (hs : ∀ i, BinaryEventSynchronized S (R.event i)) :
    NamedBinaryProjections R S := by
  obtain ⟨hA,hB,hmA,hmB⟩ := marginals_exist S
  obtain ⟨P,hP⟩ := support_exists hA
  obtain ⟨Q,hQ⟩ := support_exists hB
  refine ⟨hA,hB,P,Q,hmA,hmB,hP,hQ,?_,hs⟩
  intro i
  exact ⟨(binary_alice S (R.event i) hA hmA P hP (hs i)).1,
    (binary_bob S (R.event i) hB hmB Q hQ (hs i)).1⟩

/-- This equivalence rules out any extra completeness assumption hidden in the
explicit support-projection formulation. -/
theorem named_iff_synchronized {s} (R : Rows s) (S : NormalStrategy s) :
    NamedBinaryProjections R S ↔ ∀ i, BinaryEventSynchronized S (R.event i) := by
  constructor
  · rintro ⟨hA,hB,P,Q,hmA,hmB,hP,hQ,hsharp,hs⟩
    exact hs
  · exact named_of_synchronized R S

/-- The unselected binary outcome is also a projection on the same support. -/
theorem binary_complement (P A : Op) (hP : Projection P)
    (hA : BinaryProjectionOn P A) : Projection (P-P*A*P) := by
  have hleft : P*(P*A*P)=P*A*P := by simp only [← mul_assoc,hP.2]
  have hright : (P*A*P)*P=P*A*P := by simp only [mul_assoc,hP.2]
  constructor
  · exact (star_sub P (P*A*P)).trans
      (congrArg₂ (fun X Y : Op => X-Y) hP.1 hA.2.1)
  · rw [sub_mul,mul_sub,mul_sub,hP.2,hleft,hright,hA.2.2]
    abel

#print axioms pure_binary_analysis
#print axioms binary_alice
#print axioms binary_bob
#print axioms named_of_synchronized
#print axioms named_iff_synchronized
#print axioms binary_complement
end Sigma2.RowSynchronization
