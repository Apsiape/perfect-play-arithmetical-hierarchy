import Sigma2.UpperEntropyEffective

noncomputable section
namespace Sigma2.UpperEntropyDecision
open scoped BigOperators
open UpperRealArithmetic UpperEntropyFinite UpperEntropyEffective

/-- The explicit ordered-ring compiler interprets the finite entropy relaxation. -/
theorem codeSentence_truth (c B n k : ℕ) (η : ℚ) (a : List (ℤ × ℕ)) :
    OrderedRingTruth (codeSentence c B n k η a) ↔
      ∃ r : RawGame,Encodable.decode c=some r ∧ ∃ hr : ValidRawGame r,
        ∃ z : Data r.1 (n+1),Feasible (gameOfRaw r hr) (n+1) η z ∧
          (∑ i,(UpperEntropyPolynomial.polynomial a).eval₂ (algebraMap ℚ ℝ) (z.1 i)) ≤
            (B:ℝ)+1/(n+1:ℝ)+1/(k+1:ℝ) := by
  cases h : Encodable.decode (α := RawGame) c with
  | none => simp [codeSentence,h,OrderedRingTruth]
  | some r =>
      by_cases hr : ValidRawGame r
      · simp [codeSentence,h,hr,UpperEntropySyntax.truth_sentence r hr]
      · simp [codeSentence,h,hr,OrderedRingTruth]

/-- Decoded witnesses all refer to the same actual game, including rejection of invalid codes. -/
theorem codeSentence_truth_game (c B n k : ℕ) (η : ℚ) (a : List (ℤ × ℕ)) :
    OrderedRingTruth (codeSentence c B n k η a) ↔
      GameProperty (fun G => ∃ z : Data G.scenario (n+1),Feasible G (n+1) η z ∧
        (∑ i,(UpperEntropyPolynomial.polynomial a).eval₂ (algebraMap ℚ ℝ) (z.1 i)) ≤
          (B:ℝ)+1/(n+1:ℝ)+1/(k+1:ℝ)) c := by
  rw [codeSentence_truth]
  constructor
  · rintro ⟨r,hr,hv,z,hz,he⟩
    exact ⟨gameOfRaw r hv,by simp [decodeGame,hr,hv],z,hz,he⟩
  · rintro ⟨G,hG,hstage⟩
    unfold decodeGame at hG
    cases hr : Encodable.decode (α := RawGame) c with
    | none => simp [hr] at hG
    | some r =>
        by_cases hv : ValidRawGame r
        · have hg : gameOfRaw r hv=G := by simpa [hr,hv] using hG
          subst G
          exact ⟨r,rfl,hv,hstage⟩
        · simp [hr,hv] at hG

end Sigma2.UpperEntropyDecision
