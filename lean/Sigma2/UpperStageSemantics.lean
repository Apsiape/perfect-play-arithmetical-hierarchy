import Sigma2.UpperStageSyntax

namespace Sigma2.UpperStageSyntax
open Sigma2.UpperRealArithmetic
open scoped BigOperators ComplexOrder
noncomputable section

def Witness (s : Scenario) (κ n : ℕ) (L : ℕ → ℕ → ℕ → ℕ → Bool) : Prop :=
  ∃ (d : Fin (n+1) → ℝ)
    (E : QA s → AA s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (F : QB s → BB s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ),
    d 0=1 ∧ (∀ i,0 ≤ d i) ∧ Antitone d ∧ (∑ i,d i^2) ≤ κ ∧
    (∀ x a,(E x a).PosSemidef) ∧ (∀ y b,(F y b).PosSemidef) ∧
    (∀ x,∑ a,E x a=1) ∧ (∀ y,∑ b,F y b=1) ∧
    (∀ (x : QA s) (y : QB s) (a : AA s) (b : BB s), L x y a b = true → ∀ i j,
      ‖(E x a * Matrix.diagonal (fun k => (d k : ℂ)) * (F y b).transpose) i j‖^2 ≤ (κ:ℝ)/(n+2))

theorem models_normalization (v : ℕ → ℝ) (q a m : ℕ)
    (V : ℕ → ℕ → ℕ → ℕ → CPoly) :
    Models v (normalization q a m V) ↔
      ∀ x : Fin q, (∑ b : Fin a, ((fun i j : Fin m => ceval v (V x b i j)) : Matrix (Fin m) (Fin m) ℂ)) = (1 : Matrix (Fin m) (Fin m) ℂ) := by
  simp only [normalization,models_bounded,models_ceq,ceval_ctotal]
  constructor
  · intro h x
    ext i j
    simpa only [Finset.sum_apply,Matrix.one_apply,Fin.ext_iff,apply_ite,ceval_one,ceval_zero] using h x i j
  · intro h x i j
    have hh := congrFun (congrFun (h x) i) j
    simpa only [Finset.sum_apply,Matrix.one_apply,Fin.ext_iff,apply_ite,ceval_one,ceval_zero] using hh

theorem models_losing (v : ℕ → ℝ) (s : Scenario) (κ n : ℕ)
    (L : ℕ → ℕ → ℕ → ℕ → Bool) :
    Models v (losingConstraints (s.questionsA+1) (s.questionsB+1) (s.answersA+1) (s.answersB+1)
      (n+1) L ((κ:ℚ)/(n+2))) ↔
    ∀ (x : QA s) (y : QB s) (a : AA s) (b : BB s), L x y a b = true →
      ∀ i j, ‖(effectsE v s (n+1) x a * Matrix.diagonal (fun k => (amplitudes v (n+1) k : ℂ)) *
        (effectsF v s (n+1) y b).transpose) i j‖^2 ≤ (κ:ℝ)/(n+2) := by
  simp only [losingConstraints,models_bounded]
  constructor
  · intro h x y a b hL
    have hh := h x y a b
    rw [if_pos hL] at hh
    simp only [models_bounded,models_le,eval_constant,eval_normSq,
      ceval_sandwich v s, Rat.cast_div,Rat.cast_natCast,Rat.cast_add,Rat.cast_ofNat] at hh
    exact hh
  · intro h x y a b
    split_ifs with hL
    · simp only [models_bounded,models_le,eval_constant,eval_normSq,
        ceval_sandwich v s, Rat.cast_div,Rat.cast_natCast,Rat.cast_add,Rat.cast_ofNat]
      exact h x y a b hL
    · simp [Models]

def values (s : Scenario) (n : ℕ) (d : Fin (n+1) → ℝ)
    (Y : QA s → AA s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (Z : QB s → BB s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) : Label → ℂ
  | Sum.inl i => (d (Fin.ofNat (n+1) i) : ℂ)
  | Sum.inr (Sum.inl (x,a,i,j)) =>
      Y (Fin.ofNat _ x) (Fin.ofNat _ a) (Fin.ofNat _ i) (Fin.ofNat _ j)
  | Sum.inr (Sum.inr (y,b,i,j)) =>
      Z (Fin.ofNat _ y) (Fin.ofNat _ b) (Fin.ofNat _ i) (Fin.ofNat _ j)

theorem amplitudes_valuation (s : Scenario) (n : ℕ) (d : Fin (n+1) → ℝ)
    (Y : QA s → AA s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (Z : QB s → BB s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    amplitudes (valuation (values s n d Y Z)) (n+1) = d := by
  funext i
  have h := congrArg Complex.re (ceval_cvar_valuation (values s n d Y Z) (Sum.inl (i:ℕ)))
  simpa [amplitudes,dvar,cvar,ceval,values,Fin.ofNat_eq_cast] using h

theorem factorsY_valuation (s : Scenario) (n : ℕ) (d : Fin (n+1) → ℝ)
    (Y : QA s → AA s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (Z : QB s → BB s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (x : QA s) (a : AA s) :
    factorsY (valuation (values s n d Y Z)) s (n+1) x a = Y x a := by
  ext i j
  simpa [factorsY,yvar,values,Fin.ofNat_eq_cast] using
    ceval_cvar_valuation (values s n d Y Z) (Sum.inr (Sum.inl ((x:ℕ),(a:ℕ),(i:ℕ),(j:ℕ))))

theorem factorsZ_valuation (s : Scenario) (n : ℕ) (d : Fin (n+1) → ℝ)
    (Y : QA s → AA s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (Z : QB s → BB s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (y : QB s) (b : BB s) :
    factorsZ (valuation (values s n d Y Z)) s (n+1) y b = Z y b := by
  ext i j
  simpa [factorsZ,zvar,values,Fin.ofNat_eq_cast] using
    ceval_cvar_valuation (values s n d Y Z) (Sum.inr (Sum.inr ((y:ℕ),(b:ℕ),(i:ℕ),(j:ℕ))))

set_option maxHeartbeats 100000 in
theorem truth_sentence (s : Scenario) (κ n : ℕ) (L : ℕ → ℕ → ℕ → ℕ → Bool) :
    Truth (sentence s κ n L) ↔ Witness s κ n L := by
  classical
  have hm (v : ℕ → ℝ) : Models v (sentence s κ n L) ↔
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
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨h0,hpos,hsort,hbudget,hE,hF,hL⟩ := (hm v).mp hv
    exact ⟨amplitudes v (n+1),effectsE v s (n+1),effectsF v s (n+1),h0,hpos,hsort,hbudget,
      effectsE_pos v s (n+1),effectsF_pos v s (n+1),hE,hF,hL⟩
  · rintro ⟨d,E,F,h0,hpos,hsort,hbudget,hEpos,hFpos,hE,hF,hL⟩
    choose Y hY using fun x a => (positive_iff_factor (E x a)).mp (hEpos x a)
    choose Z hZ using fun y b => (positive_iff_factor (F y b)).mp (hFpos y b)
    let v := valuation (values s n d Y Z)
    have hd : amplitudes v (n+1) = d := amplitudes_valuation s n d Y Z
    have he : effectsE v s (n+1) = E := by
      funext x a
      rw [effectsE_eq,factorsY_valuation]
      exact (hY x a).symm
    have hf : effectsF v s (n+1) = F := by
      funext y b
      rw [effectsF_eq,factorsZ_valuation]
      exact (hZ y b).symm
    refine ⟨v,(hm v).mpr ?_⟩
    rw [hd,he,hf]
    exact ⟨h0,hpos,hsort,hbudget,hE,hF,hL⟩

end
end Sigma2.UpperStageSyntax
