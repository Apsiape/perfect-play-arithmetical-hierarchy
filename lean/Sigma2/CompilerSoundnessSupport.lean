import Sigma2.CompilerSoundnessNames
import Sigma2.RowSoundnessComplete

/-! State-support preservation of padded-answer normalization, and its concrete
call site at the existing Boolean RowGame restriction. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace Sigma2.CompilerSoundnessSupport
open Compiler CompilerScaffold CompilerSoundnessPadding Preliminaries TensorLifts CoarseCells
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

theorem sum_single (E : Answer → Op) (a : Answer) :
    (∑ b : Answer,if b=a then E b else 0)=E a := by simp

theorem pure_zero_alice {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (e : Op) (he : SupportOf h e)
    (x : QA s) (a : AA s) (y : QB s) (hz : ∀ b,S.probability x y a b=0) :
    e*S.measurements.alice x a*e=0 := by
  have hs : (∑ b,S.probability x y a b)=
      (inner ℂ S.vector (left (S.measurements.alice x a) S.vector)).re := by
    simp only [PureStrategy.probability,← complex_re_sum,← inner_sum,← sum_apply,
      ← Finset.mul_sum,S.measurements.right_sum,mul_one,measurements_left]
  have hx : (inner ℂ S.vector (left (S.measurements.alice x a) S.vector)).re=0 := by
    rw [← hs]; simp only [hz,Finset.sum_const_zero]
  have hh := PureSupport.zero_on_support S h hm e he _ (S.measurements.alice_pos x a) hx
  rw [mul_assoc,hh.1,mul_zero]

theorem zero_alice {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalA S h) (e : Op) (he : SupportOf h e)
    (x : QA s) (a : AA s) (y : QB s) (hz : ∀ b,S.probability x y a b=0) :
    e*S.measurements.alice x a*e=0 := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  simpa only [hA] using pure_zero_alice T h (hM h hm) e he x a y
    (fun b => (hprob x y a b).symm.trans (hz b))

theorem zero_bob {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalB S h) (e : Op) (he : SupportOf h e)
    (y : QB s) (b : BB s) (x : QA s) (hz : ∀ a,S.probability x y a b=0) :
    e*S.measurements.bob y b*e=0 := by
  obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
  have hh := pure_zero_alice (PureTransfer.flipPure T) h (hM h hm) e he y b x
    (fun a => (PureTransfer.flipPure_probability T x y a b).trans
      ((hprob x y a b).symm.trans (hz a)))
  simpa only [PureTransfer.flipPure,PureTransfer.flipMeasurements,hB,
    Purification.measurements,TensorLifts.measurements] using hh

theorem alice_support (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (x : QA (scenario P)) (a : AA (scenario P)) :
    e*(normalize P S).measurements.alice x a*e=e*S.measurements.alice x a*e := by
  change e*coarse (S.measurements.alice x) (fold (question P x.val)) a*e=_
  simp only [coarse,Finset.mul_sum,Finset.sum_mul]
  have ht (aa : Answer) :
      e*(if fold (question P x.val) aa=a then S.measurements.alice x aa else 0)*e=
        if aa=a then e*S.measurements.alice x aa*e else 0 := by
    by_cases ha : valid (question P x.val) aa.val=true
    · rw [fold_valid _ _ ha]
      split_ifs <;> simp
    · have hz := zero_alice S h hm e he x aa 0
        (fun b => invalid_probability P S hS x 0 aa b (Or.inl (Bool.eq_false_iff.mpr ha)))
      split_ifs <;> simp_all only [mul_zero,zero_mul,hz,ite_true,ite_false]
  simp_rw [ht]
  exact sum_single _ _

theorem bob_support (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalB S h)
    (e : Op) (he : SupportOf h e) (y : QB (scenario P)) (b : BB (scenario P)) :
    e*(normalize P S).measurements.bob y b*e=e*S.measurements.bob y b*e := by
  change e*coarse (S.measurements.bob y) (fold (question P y.val)) b*e=_
  simp only [coarse,Finset.mul_sum,Finset.sum_mul]
  have ht (bb : Answer) :
      e*(if fold (question P y.val) bb=b then S.measurements.bob y bb else 0)*e=
        if bb=b then e*S.measurements.bob y bb*e else 0 := by
    by_cases hb : valid (question P y.val) bb.val=true
    · rw [fold_valid _ _ hb]
      split_ifs <;> simp
    · have hz := zero_bob S h hm e he y bb 0
        (fun a => invalid_probability P S hS 0 y a bb (Or.inr (Bool.eq_false_iff.mpr hb)))
      split_ifs <;> simp_all only [mul_zero,zero_mul,hz,ite_true,ite_false]
  simp_rw [ht]
  exact sum_single _ _

theorem binary_alice (P : Presentation) (S : NormalStrategy (scenario P))
    (i : Fin (names P).length) (a : AA (scenario P)) :
    (normalize P S).measurements.alice (event P i).x a=S.measurements.alice (event P i).x a := by
  change coarse _ (fold (question P (event P i).x.val)) a=_
  rw [CompilerSoundnessNames.question_event]
  simp only [fold,coarse]
  exact sum_single _ _

theorem binary_bob (P : Presentation) (S : NormalStrategy (scenario P))
    (i : Fin (names P).length) (b : BB (scenario P)) :
    (normalize P S).measurements.bob (event P i).y b=S.measurements.bob (event P i).y b := by
  change coarse _ (fold (question P (event P i).x.val)) b=_
  rw [CompilerSoundnessNames.question_event]
  simp only [fold,coarse]
  exact sum_single _ _

theorem rowsHold (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (hR : RowsHold (rows P) S) :
    RowsHold (rows P) (normalize P S) := by
  obtain ⟨hA,hB,hmA,hmB,hmirror,hrowsA,hrowsB⟩ := hR
  refine ⟨hA,hB,hmA,hmB,?_,?_,?_⟩
  · intro i k hk
    have hh := hmirror i k hk
    rw [measurements_left,measurements_right] at hh ⊢
    have hvec : (normalize P S).vector=S.vector := rfl
    simpa only [rows,binary_alice,binary_bob,hvec] using hh
  · intro r
    simpa only [rows,binary_alice] using hrowsA r
  · intro r
    simpa only [rows,binary_bob] using hrowsB r

/-- An actual final-game perfect strategy supplies one normalized pre-strategy,
its actual row equations, synchronized dictionary and all four FMS instances. -/
theorem from_final (P : Presentation) (T : NormalStrategy (finalGame P).scenario)
    (hT : Perfect (finalGame P) T) :
    ∃ S : NormalStrategy (scenario P),
      Perfect (preGame P) S ∧ RowsHold (rows P) S ∧ NamedBinaryProjections (rows P) S ∧
      (∀ g : Fin 4,ConditionalPerfect S (fmsInstance P g)) ∧
      Extends (RowGame.embedding (preGame P) (rows P)) S T ∧
      (FiniteMarginalEntropy S ↔ FiniteMarginalEntropy T) := by
  have hs := RowSoundness.soundness (preGame P) (rows P) T hT
  let U := RowRestriction.restrict (preGame P) (rows P) T
  have hU : Perfect (preGame P) U := hs.1
  refine ⟨normalize P U,perfect P U hU,rowsHold P U hU hs.2.2.1,
    CompilerSoundnessNames.named P _ (perfect P U hU),conditionalPerfect P U hU,?_,Iff.rfl⟩
  intro x y a b
  exact (probability P U hU x y a b).trans (hs.2.1 x y a b)

#print axioms alice_support
#print axioms bob_support
#print axioms rowsHold
#print axioms from_final
end Sigma2.CompilerSoundnessSupport
