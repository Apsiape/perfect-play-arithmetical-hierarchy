import Sigma2.UpperGridCertificate
import Sigma2.UpperStageSemantics
import Sigma2.UpperEntropySyntax
import Sigma2.UpperEntropyEffective

/-! Both compiled stage sentences are satisfiable in the unit box whenever they are
satisfiable at all. Amplitudes and probabilities lie in `[0,1]`, and a Gram factor `Y`
of an effect `E = Yᴴ Y` from a POVM summing to the identity has entries of modulus at
most one. Re-encoding a witness through these factors bounds every coordinate, so stage
truth is bounded truth, which the grid certificate makes uniformly Π⁰₁. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace Sigma2.UpperBoxStages
open Sigma2.UpperRealArithmetic Sigma2.UpperGridCertificate Sigma2.UpperStageSyntax
open Sigma2.UpperGameCompiler Sigma2.UpperEntropyFinite
open scoped BigOperators ComplexOrder

theorem valuation_bound {α : Type*} [Encodable α] (z : α → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ a, |(z a).re| ≤ B ∧ |(z a).im| ≤ B) (k : ℕ) : |valuation z k| ≤ B := by
  have hx : |(((Encodable.decode (α := α) (k/2)).map z).getD 0).re| ≤ B ∧
      |(((Encodable.decode (α := α) (k/2)).map z).getD 0).im| ≤ B := by
    cases Encodable.decode (α := α) (k/2) with
    | none => simp [hB]
    | some a => simpa using h a
  unfold valuation
  dsimp only
  split_ifs
  · exact hx.1
  · exact hx.2

theorem gram_entry_bound {ι : Type*} [Fintype ι] {m : ℕ} (Y : ι → Matrix (Fin m) (Fin m) ℂ)
    (h : ∑ b, (Y b).conjTranspose * Y b = 1) (b : ι) (k i : Fin m) : ‖Y b k i‖ ≤ 1 := by
  have hii := congrFun (congrFun h i) i
  rw [Matrix.sum_apply, Matrix.one_apply_eq] at hii
  have hre := congrArg Complex.re hii
  have hterm (z : ℂ) : (star z * z).re = ‖z‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Complex.mul_re]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum, Complex.one_re,
    hterm] at hre
  have h1 : ‖Y b k i‖^2 ≤ ∑ k', ‖Y b k' i‖^2 :=
    Finset.single_le_sum (f := fun k' => ‖Y b k' i‖^2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ k)
  have h2 : ∑ k', ‖Y b k' i‖^2 ≤ ∑ b', ∑ k', ‖Y b' k' i‖^2 :=
    Finset.single_le_sum (f := fun b' => ∑ k', ‖Y b' k' i‖^2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ b)
  have h3 : ‖Y b k i‖^2 ≤ 1 := by linarith
  nlinarith [norm_nonneg (Y b k i)]

theorem factor_bound {ι : Type*} [Fintype ι] {m : ℕ} (Y : ι → Matrix (Fin m) (Fin m) ℂ)
    (h : ∑ b, (Y b).conjTranspose * Y b = 1) (b : ι) (k i : Fin m) :
    |(Y b k i).re| ≤ 1 ∧ |(Y b k i).im| ≤ 1 :=
  ⟨(Complex.abs_re_le_norm _).trans (gram_entry_bound Y h b k i),
    (Complex.abs_im_le_norm _).trans (gram_entry_bound Y h b k i)⟩

/-! ### The finite Schmidt stage -/

theorem models_stage_iff (v : ℕ → ℝ) (s : Scenario) (κ n : ℕ) (L : ℕ → ℕ → ℕ → ℕ → Bool) :
    Models v (sentence s κ n L) ↔
      amplitudes v (n+1) 0=1 ∧ (∀ i,0 ≤ amplitudes v (n+1) i) ∧
      Antitone (amplitudes v (n+1)) ∧ (∑ i,amplitudes v (n+1) i^2) ≤ κ ∧
      (∀ x,∑ a,effectsE v s (n+1) x a=1) ∧
      (∀ y,∑ b,effectsF v s (n+1) y b=1) ∧
      (∀ (x : QA s) (y : QB s) (a : AA s) (b : BB s), L x y a b = true → ∀ i j,
        ‖(effectsE v s (n+1) x a * Matrix.diagonal (fun k => (amplitudes v (n+1) k : ℂ)) *
          (effectsF v s (n+1) y b).transpose) i j‖^2 ≤ (κ:ℝ)/(n+2)) := by
  have he : Models v (normalization (s.questionsA+1) (s.answersA+1) (n+1) (evar (n+1))) ↔
      ∀ x, ∑ a,effectsE v s (n+1) x a = 1 := models_normalization v _ _ _ _
  have hf : Models v (normalization (s.questionsB+1) (s.answersB+1) (n+1) (fvar (n+1))) ↔
      ∀ y, ∑ b,effectsF v s (n+1) y b = 1 := models_normalization v _ _ _ _
  rw [sentence,models_append,models_append,models_append,models_amplitude,he,hf,models_losing]
  constructor
  · rintro ⟨⟨⟨⟨h0,hp,ha,hb⟩,he⟩,hf⟩,hl⟩
    exact ⟨h0,hp,ha,hb,he,hf,hl⟩
  · rintro ⟨h0,hp,ha,hb,he,hf,hl⟩
    exact ⟨⟨⟨⟨h0,hp,ha,hb⟩,he⟩,hf⟩,hl⟩

/-- Every model of the finite-stage sentence has a re-encoded model in the unit box. -/
theorem stage_boxTruth (s : Scenario) (κ n : ℕ) (L : ℕ → ℕ → ℕ → ℕ → Bool) :
    Truth (sentence s κ n L) ↔ BoxTruth 1 (sentence s κ n L) := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨h0, hpos, hsort, _, hE, hF, _⟩ := (models_stage_iff v s κ n L).mp hv
    let w := valuation (UpperStageSyntax.values s n (amplitudes v (n+1))
      (factorsY v s (n+1)) (factorsZ v s (n+1)))
    have hd : amplitudes w (n+1) = amplitudes v (n+1) := amplitudes_valuation _ _ _ _ _
    have he : effectsE w s (n+1) = effectsE v s (n+1) := by
      funext x a
      rw [effectsE_eq, effectsE_eq, factorsY_valuation]
    have hf : effectsF w s (n+1) = effectsF v s (n+1) := by
      funext y b
      rw [effectsF_eq, effectsF_eq, factorsZ_valuation]
    have hY (x : QA s) : ∑ a, (factorsY v s (n+1) x a).conjTranspose * factorsY v s (n+1) x a = 1 := by
      have := hE x
      simp only [effectsE_eq] at this
      exact this
    have hZ (y : QB s) : ∑ b, (factorsZ v s (n+1) y b).conjTranspose * factorsZ v s (n+1) y b = 1 := by
      have := hF y
      simp only [effectsF_eq] at this
      exact this
    refine ⟨w, ?_, ?_⟩
    · intro k
      have hb := valuation_bound (UpperStageSyntax.values s n (amplitudes v (n+1))
        (factorsY v s (n+1)) (factorsZ v s (n+1))) 1 zero_le_one ?_ k
      · simpa using hb
      rintro (i | ⟨x, a, i, j⟩ | ⟨y, b, i, j⟩)
      · simp only [UpperStageSyntax.values, Complex.ofReal_re, Complex.ofReal_im, abs_zero,
          zero_le_one, and_true]
        have hle := hsort (Fin.zero_le (Fin.ofNat (n+1) i))
        rw [h0] at hle
        rw [abs_le]
        constructor <;> linarith [hpos (Fin.ofNat (n+1) i)]
      · exact factor_bound _ (hY _) _ _ _
      · exact factor_bound _ (hZ _) _ _ _
    · exact (models_stage_iff w s κ n L).mpr (by rw [hd, he, hf]; exact (models_stage_iff v s κ n L).mp hv)
  · rintro ⟨v, _, hv⟩
    exact ⟨v, hv⟩

/-! ### The finite entropy relaxation -/

theorem models_entropy_iff (r : RawGame) (hr : ValidRawGame r) (B n k : ℕ)
    (η : ℚ) (a : List (ℤ × ℕ)) (v : ℕ → ℝ) :
    Models v (UpperEntropySyntax.sentence r B n k η a) ↔
      Feasible (gameOfRaw r hr) (n+1) η (UpperEntropySyntax.data v r.1 (n+1)) ∧
        (∑ i,(UpperEntropyPolynomial.polynomial a).eval₂ (algebraMap ℚ ℝ)
          ((UpperEntropySyntax.data v r.1 (n+1)).1 i)) ≤ (B:ℝ)+1/(n+1:ℝ)+1/(k+1:ℝ) := by
  have hE := models_normalization v (r.1.questionsA+1) (r.1.answersA+1) (n+1) (evar (n+1))
  have hF := models_normalization v (r.1.questionsB+1) (r.1.answersB+1) (n+1) (fvar (n+1))
  simp only [UpperEntropySyntax.sentence,models_append,UpperEntropySyntax.models_simplex,models_le,
    eval_rtotal,UpperEntropySyntax.eval_approximation,eval_constant,
    UpperEntropySyntax.eval_loss v r hr,
    Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] at *
  change _ ↔ Feasible _ _ _ _ ∧ _
  rw [hE,hF]
  simp only [Feasible,UpperEntropySyntax.data]
  have hpE := effectsE_pos v r.1 (n+1)
  have hpF := effectsF_pos v r.1 (n+1)
  constructor
  · rintro ⟨⟨⟨⟨⟨hp,hs,ha,ht⟩,hEs⟩,hFs⟩,hl⟩,he⟩
    exact ⟨⟨hp,hs,ha,ht,hpE,hpF,hEs,hFs,hl⟩,he⟩
  · rintro ⟨⟨hp,hs,ha,ht,_,_,hEs,hFs,hl⟩,he⟩
    exact ⟨⟨⟨⟨⟨hp,hs,ha,ht⟩,hEs⟩,hFs⟩,hl⟩,he⟩

/-- Every model of the entropy-relaxation sentence has a re-encoded model in the unit box. -/
theorem entropy_boxTruth (r : RawGame) (hr : ValidRawGame r) (B n k : ℕ)
    (η : ℚ) (a : List (ℤ × ℕ)) :
    Truth (UpperEntropySyntax.sentence r B n k η a) ↔
      BoxTruth 1 (UpperEntropySyntax.sentence r B n k η a) := by
  constructor
  · rintro ⟨v, hv⟩
    have hm := (models_entropy_iff r hr B n k η a v).mp hv
    obtain ⟨⟨hp, hs, _, ht, _, _, hEs, hFs, _⟩, _⟩ := hm
    simp only [UpperEntropySyntax.data] at hp hs ht hEs hFs
    let w := valuation (UpperEntropySyntax.values r.1 n (UpperEntropySyntax.probabilities v (n+1))
      (amplitudes v (n+1)) (factorsY v r.1 (n+1)) (factorsZ v r.1 (n+1)))
    have hdata : UpperEntropySyntax.data w r.1 (n+1) = UpperEntropySyntax.data v r.1 (n+1) := by
      rw [UpperEntropySyntax.data_valuation]
      have hE' : (fun x a => (factorsY v r.1 (n+1) x a).conjTranspose * factorsY v r.1 (n+1) x a) =
          effectsE v r.1 (n+1) := by
        funext x a
        exact (effectsE_eq v r.1 (n+1) x a).symm
      have hF' : (fun y b => (factorsZ v r.1 (n+1) y b).conjTranspose * factorsZ v r.1 (n+1) y b) =
          effectsF v r.1 (n+1) := by
        funext y b
        exact (effectsF_eq v r.1 (n+1) y b).symm
      rw [hE', hF']
      rfl
    have hY (x : QA r.1) :
        ∑ a, (factorsY v r.1 (n+1) x a).conjTranspose * factorsY v r.1 (n+1) x a = 1 := by
      have := hEs x
      simp only [effectsE_eq] at this
      exact this
    have hZ (y : QB r.1) :
        ∑ b, (factorsZ v r.1 (n+1) y b).conjTranspose * factorsZ v r.1 (n+1) y b = 1 := by
      have := hFs y
      simp only [effectsF_eq] at this
      exact this
    refine ⟨w, ?_, ?_⟩
    · intro k
      have hb := valuation_bound (UpperEntropySyntax.values r.1 n
        (UpperEntropySyntax.probabilities v (n+1)) (amplitudes v (n+1))
        (factorsY v r.1 (n+1)) (factorsZ v r.1 (n+1))) 1 zero_le_one ?_ k
      · simpa using hb
      rintro (i | ⟨x, a, i, j⟩ | ⟨y, b, i, j⟩)
      · simp only [UpperEntropySyntax.values]
        set j := Fin.ofNat (n+1) i
        have hp1 : UpperEntropySyntax.probabilities v (n+1) j ≤ 1 := by
          rw [← hs]
          exact Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ j)
        obtain ⟨ht0, ht2⟩ := ht j
        have ht1 : amplitudes v (n+1) j ≤ 1 := by nlinarith
        refine ⟨abs_le.mpr ⟨by linarith, ht1⟩, abs_le.mpr ⟨by linarith [hp j], hp1⟩⟩
      · exact factor_bound _ (hY _) _ _ _
      · exact factor_bound _ (hZ _) _ _ _
    · exact (models_entropy_iff r hr B n k η a w).mpr
        (by rw [hdata]; exact (models_entropy_iff r hr B n k η a v).mp hv)
  · rintro ⟨v, _, hv⟩
    exact ⟨v, hv⟩

/-! ### Compiled codes -/

/-- The conjunctive clause of a compiled sentence; the empty disjunction becomes `0 ≤ -1`. -/
def unwrap (S : OrderedRingSentence) : Sentence :=
  (S.head?.map fun c => c.map Prod.snd).getD [(false, constant (-1))]

theorem unwrap_primrec : Primrec unwrap :=
  Primrec.option_getD.comp (Primrec.option_map Primrec.list_head?
    (Primrec.list_map Primrec.snd (Primrec.snd.comp Primrec.snd).to₂).to₂) (Primrec.const _)

theorem unwrap_conjunctive (s : Sentence) : unwrap (conjunctive s) = s := by
  simp [unwrap, conjunctive, List.map_map, Function.comp_def]

theorem not_boxTruth_unwrap_nil (B : ℕ) : ¬ BoxTruth B (unwrap []) := by
  rintro ⟨v, _, h⟩
  have := h (false, constant (-1)) (by simp [unwrap])
  simp [holds] at this
  linarith

theorem stage_code_box (c κ n : ℕ) :
    OrderedRingTruth (UpperGameCompiler.codeSentence c κ n) ↔
      BoxTruth 1 (unwrap (UpperGameCompiler.codeSentence c κ n)) := by
  unfold UpperGameCompiler.codeSentence
  cases h : Encodable.decode (α := RawGame) c with
  | none => simp [OrderedRingTruth, not_boxTruth_unwrap_nil]
  | some r =>
    by_cases hr : ValidRawGame r
    · simp only [Option.map_some, Option.getD_some, hr, ↓reduceIte, truth_conjunctive,
        unwrap_conjunctive]
      exact stage_boxTruth _ _ _ _
    · simp [hr, OrderedRingTruth, not_boxTruth_unwrap_nil]

theorem entropy_code_box (c B n k : ℕ) (η : ℚ) (a : List (ℤ × ℕ)) :
    OrderedRingTruth (UpperEntropyEffective.codeSentence c B n k η a) ↔
      BoxTruth 1 (unwrap (UpperEntropyEffective.codeSentence c B n k η a)) := by
  unfold UpperEntropyEffective.codeSentence
  cases h : Encodable.decode (α := RawGame) c with
  | none => simp [OrderedRingTruth, not_boxTruth_unwrap_nil]
  | some r =>
    by_cases hr : ValidRawGame r
    · simp only [Option.map_some, Option.getD_some, hr, ↓reduceIte, truth_conjunctive,
        unwrap_conjunctive]
      exact entropy_boxTruth r hr _ _ _ _ _
    · simp [hr, OrderedRingTruth, not_boxTruth_unwrap_nil]

end Sigma2.UpperBoxStages
