import Sigma2.RowScalarOld

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries CoarseCells FiniteSpectral TensorLifts

private theorem pure_zero_effect {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x : QA s) (a : AA s) (y : QB s) (hz : ∀ b,S.probability x y a b=0) :
    P*S.measurements.alice x a*P=0 := by
  have hs : (∑ b,S.probability x y a b)=
      (inner ℂ S.vector (left (S.measurements.alice x a) S.vector)).re := by
    simp only [PureStrategy.probability,← complex_re_sum,← inner_sum,← sum_apply,
      ← Finset.mul_sum,S.measurements.right_sum,mul_one,measurements_left]
  have he : (inner ℂ S.vector (left (S.measurements.alice x a) S.vector)).re=0 := by
    rw [← hs]
    simp only [hz,Finset.sum_const_zero]
  have hh := PureSupport.zero_on_support S h hm P hP _ (S.measurements.alice_pos x a) he
  rw [mul_assoc,hh.1,mul_zero]

private theorem normal_zero_alice {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (x : QA s) (a : AA s) (y : QB s) (hz : ∀ b,S.probability x y a b=0) :
    P*S.measurements.alice x a*P=0 := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  simpa only [hA] using pure_zero_effect T h (hM h hm) P hP x a y
    (fun b => (hprob x y a b).symm.trans (hz b))

private theorem normal_zero_bob {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q)
    (y : QB s) (b : BB s) (x : QA s) (hz : ∀ a,S.probability x y a b=0) :
    Q*S.measurements.bob y b*Q=0 := by
  obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
  have hh := pure_zero_effect (PureTransfer.flipPure T) h (hM h hm) Q hQ y b x
    (fun a => (PureTransfer.flipPure_probability T x y a b).trans
      ((hprob x y a b).symm.trans (hz a)))
  simpa only [PureTransfer.flipPure,PureTransfer.flipMeasurements,hB,
    Purification.measurements,TensorLifts.measurements] using hh

/-- Folding invalid old answers into zero changes no supported old effect.
This includes old answer zero itself, so no hidden padding projection remains. -/
theorem restriction_alice_effect (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (x : QA G.scenario) (a : AA G.scenario) :
    P*(RowRestriction.restrict G R S).measurements.alice x a*P=
      P*S.measurements.alice ((embedding G R).qA x) ((embedding G R).aA a)*P := by
  change P*coarse (S.measurements.alice ((embedding G R).qA x)) (RowRestriction.foldA G R) a*P=_
  simp only [coarse,Finset.mul_sum,Finset.sum_mul]
  have ht (aa : AA (scenario G R)) :
      P*(if RowRestriction.foldA G R aa=a then S.measurements.alice ((embedding G R).qA x) aa else 0)*P=
        if aa=(embedding G R).aA a then
          P*S.measurements.alice ((embedding G R).qA x) aa*P else 0 := by
    by_cases ha : aa.val<G.scenario.answersA+1
    · have he : RowRestriction.foldA G R aa=a ↔ aa=(embedding G R).aA a := by
        simp only [RowRestriction.foldA,ha,dite_true,embedding,Fin.ext_iff]
      simp only [he]
      split_ifs <;> simp
    · have hz := normal_zero_alice S h hm P hP ((embedding G R).qA x) aa
        ((embedding G R).qB 0)
        (fun b => RowRestriction.padded_probability G R S hS x 0 aa b (Or.inl (by omega)))
      have hn : aa≠(embedding G R).aA a := by
        intro he
        have hv := congrArg Fin.val he
        have := a.isLt
        simp only [embedding] at hv
        omega
      split_ifs <;> simp_all only [mul_zero,zero_mul,hz,ite_false]
  simp_rw [ht]
  simp

theorem restriction_bob_effect (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q)
    (y : QB G.scenario) (b : BB G.scenario) :
    Q*(RowRestriction.restrict G R S).measurements.bob y b*Q=
      Q*S.measurements.bob ((embedding G R).qB y) ((embedding G R).aB b)*Q := by
  change Q*coarse (S.measurements.bob ((embedding G R).qB y)) (RowRestriction.foldB G R) b*Q=_
  simp only [coarse,Finset.mul_sum,Finset.sum_mul]
  have ht (bb : BB (scenario G R)) :
      Q*(if RowRestriction.foldB G R bb=b then S.measurements.bob ((embedding G R).qB y) bb else 0)*Q=
        if bb=(embedding G R).aB b then
          Q*S.measurements.bob ((embedding G R).qB y) bb*Q else 0 := by
    by_cases hb : bb.val<G.scenario.answersB+1
    · have he : RowRestriction.foldB G R bb=b ↔ bb=(embedding G R).aB b := by
        simp only [RowRestriction.foldB,hb,dite_true,embedding,Fin.ext_iff]
      simp only [he]
      split_ifs <;> simp
    · have hz := normal_zero_bob S h hm Q hQ ((embedding G R).qB y) bb
        ((embedding G R).qA 0)
        (fun a => RowRestriction.padded_probability G R S hS 0 y a bb (Or.inr (by omega)))
      have hn : bb≠(embedding G R).aB b := by
        intro he
        have hv := congrArg Fin.val he
        have := b.isLt
        simp only [embedding] at hv
        omega
      split_ifs <;> simp_all only [mul_zero,zero_mul,hz,ite_false]
  simp_rw [ht]
  simp

#print axioms restriction_alice_effect
#print axioms restriction_bob_effect
#print axioms pure_zero_effect
#print axioms normal_zero_alice
#print axioms normal_zero_bob

end Sigma2.RowScalar