import Sigma2.UpperEntropyFinite
import Sigma2.UpperEntropyPolynomial
import Sigma2.UpperGameDecision

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators ComplexOrder
namespace Sigma2.UpperEntropySyntax
open UpperRealArithmetic UpperStageSyntax UpperGameCompiler UpperEntropyFinite

/-- Probability coordinates use the imaginary part of the amplitude label. -/
def pvar (i : ℕ) : Poly := var (2*Encodable.encode (Sum.inl i : Label)+1)

def power (p : Poly) (k : ℕ) : Poly := Nat.rec (constant 1) (fun _ q => mul p q) k

@[simp] theorem eval_power (v : ℕ → ℝ) (p : Poly) (k : ℕ) :
    eval v (power p k)=eval v p^k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
      change eval v (mul p (power p k))=eval v p^(k+1)
      rw [eval_mul,ih,pow_succ]
      ring

def coefficient (a : List (ℤ × ℕ)) (i : ℕ) : ℚ :=
  (((a[i]?.getD (0,0)).1:ℤ):ℚ)/((a[i]?.getD (0,0)).2+1)

def approximation (a : List (ℤ × ℕ)) (p : Poly) : Poly :=
  rtotal a.length fun i => mul (constant (coefficient a i)) (power p i)

@[simp] theorem eval_approximation (v : ℕ → ℝ) (a : List (ℤ × ℕ)) (p : Poly) :
    eval v (approximation a p)=
      (UpperEntropyPolynomial.polynomial a).eval₂ (algebraMap ℚ ℝ) (eval v p) := by
  rw [approximation,eval_rtotal,UpperEntropyPolynomial.eval_polynomial]
  simp only [eval_mul,eval_constant,eval_power]
  rw [← sum_range_fin a.length (fun i => (coefficient a i:ℝ)*eval v p^i)]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map,List.length_range] at hi
    simp [coefficient,hi]

def simplex (m : ℕ) : Sentence :=
  bounded m (fun i => le (constant 0) (pvar i)) ++
  eq (rtotal m pvar) (constant 1) ++
  bounded m (fun i => bounded m fun j => if i ≤ j then le (pvar j) (pvar i) else []) ++
  bounded m (fun i => le (constant 0) (dvar i) ++ eq (mul (dvar i) (dvar i)) (pvar i))

def event (m x y a b : ℕ) : CPoly :=
  ctotal m fun i => ctotal m fun j =>
    cmul (cmul (cmul (dvar i,constant 0) (dvar j,constant 0))
      (evar m x a i j)) (fvar m y b i j)

def lossPoly (r : RawGame) (m : ℕ) : Poly :=
  rtotal (r.1.questionsA+1) fun x => rtotal (r.1.questionsB+1) fun y =>
    rtotal (r.1.answersA+1) fun a => rtotal (r.1.answersB+1) fun b =>
      if rawWin r x y a b then constant 0 else
        mul (constant (rawWeight r x y)) (event m x y a b).1

def sentence (r : RawGame) (B n k : ℕ) (η : ℚ) (a : List (ℤ × ℕ)) : Sentence :=
  simplex (n+1) ++
  normalization (r.1.questionsA+1) (r.1.answersA+1) (n+1) (evar (n+1)) ++
  normalization (r.1.questionsB+1) (r.1.answersB+1) (n+1) (fvar (n+1)) ++
  le (lossPoly r (n+1)) (constant η) ++
  le (rtotal (n+1) fun i => approximation a (pvar i))
    (constant ((B:ℚ)+1/(n+1:ℚ)+1/(k+1:ℚ)))

def probabilities (v : ℕ → ℝ) (m : ℕ) : Fin m → ℝ := fun i => eval v (pvar i)

def data (v : ℕ → ℝ) (s : Scenario) (m : ℕ) : Data s m :=
  (probabilities v m,amplitudes v m,effectsE v s m,effectsF v s m)

theorem models_simplex (v : ℕ → ℝ) (m : ℕ) :
    Models v (simplex m) ↔
      (∀ i,0 ≤ probabilities v m i) ∧ (∑ i,probabilities v m i)=1 ∧
      Antitone (probabilities v m) ∧
      (∀ i,0 ≤ amplitudes v m i ∧ amplitudes v m i^2=probabilities v m i) := by
  simp only [simplex,models_append,models_bounded,models_eq,models_le,
    eval_rtotal,eval_constant,eval_mul,Rat.cast_zero,Rat.cast_one]
  have ha : (∀ i j : Fin m,Models v (if (i:ℕ) ≤ j then le (pvar j) (pvar i) else [])) ↔
      Antitone (probabilities v m) := by
    constructor
    · intro h i j hij
      have hh := h i j
      rw [ite_eq_left (show (i:ℕ) ≤ j from hij),models_le] at hh
      exact hh
    · intro h i j
      split_ifs with hij
      · exact (models_le _ _ _).mpr (h hij)
      · simp [Models]
  rw [ha]
  simp only [probabilities,amplitudes,pow_two]
  tauto

@[simp] theorem ceval_amplitude (v : ℕ → ℝ) (i : ℕ) :
    ceval v (dvar i,constant 0)=(eval v (dvar i):ℂ) := by
  apply Complex.ext <;> simp [ceval]

@[simp] theorem ceval_event (v : ℕ → ℝ) (s : Scenario) (m : ℕ)
    (x : QA s) (y : QB s) (a : AA s) (b : BB s) :
    ceval v (event m x y a b)=
      ∑ i,∑ j,(amplitudes v m i:ℂ)*(amplitudes v m j:ℂ)*
        effectsE v s m x a i j*effectsF v s m y b i j := by
  simp [event,amplitudes,effectsE,effectsF]

@[simp] theorem eval_loss (v : ℕ → ℝ) (r : RawGame) (hr : ValidRawGame r) (m : ℕ) :
    eval v (lossPoly r m)=finiteLoss (gameOfRaw r hr) m (data v r.1 m) := by
  simp only [lossPoly,eval_rtotal,finiteLoss,data,gameOfRaw]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change eval v (if rawAccepts r x y a b then constant 0 else
    mul (constant (rawDistribution r x y)) (event m x y a b).1)=_
  by_cases hw : rawAccepts r x y a b=true
  · simp only [hw,ite_true,eval_constant,Rat.cast_zero]
  · simp only [hw,Bool.false_eq_true,ite_false,eval_mul,eval_constant]
    change (rawDistribution r x y:ℝ)*(ceval v (event m x y a b)).re=_
    rw [ceval_event v r.1]

def values (s : Scenario) (n : ℕ) (p t : Fin (n+1) → ℝ)
    (Y : QA s → AA s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (Z : QB s → BB s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) : Label → ℂ
  | .inl i => ⟨t (Fin.ofNat (n+1) i),p (Fin.ofNat (n+1) i)⟩
  | .inr (.inl (x,a,i,j)) =>
      Y (Fin.ofNat _ x) (Fin.ofNat _ a) (Fin.ofNat _ i) (Fin.ofNat _ j)
  | .inr (.inr (y,b,i,j)) =>
      Z (Fin.ofNat _ y) (Fin.ofNat _ b) (Fin.ofNat _ i) (Fin.ofNat _ j)

theorem data_valuation (s : Scenario) (n : ℕ) (p t : Fin (n+1) → ℝ)
    (Y : QA s → AA s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (Z : QB s → BB s → Matrix (Fin (n+1)) (Fin (n+1)) ℂ) :
    data (valuation (values s n p t Y Z)) s (n+1)=
      (p,t,(fun x a => (Y x a).conjTranspose*Y x a),
        (fun y b => (Z y b).conjTranspose*Z y b)) := by
  apply Prod.ext
  · funext i
    have hh := congrArg Complex.im
      (ceval_cvar_valuation (values s n p t Y Z) (.inl (i:ℕ)))
    simpa [data,probabilities,pvar,cvar,ceval,values,Fin.ofNat_eq_cast] using hh
  · apply Prod.ext
    · funext i
      have hh := congrArg Complex.re
        (ceval_cvar_valuation (values s n p t Y Z) (.inl (i:ℕ)))
      simpa [data,amplitudes,dvar,cvar,ceval,values,Fin.ofNat_eq_cast] using hh
    · apply Prod.ext
      · funext x a
        rw [show (data (valuation (values s n p t Y Z)) s (n+1)).2.2.1 x a=
          effectsE (valuation (values s n p t Y Z)) s (n+1) x a from rfl,effectsE_eq]
        suffices factorsY (valuation (values s n p t Y Z)) s (n+1) x a=Y x a by rw [this]
        ext i j
        simpa [factorsY,yvar,values,Fin.ofNat_eq_cast] using
          ceval_cvar_valuation (values s n p t Y Z) (.inr (.inl ((x:ℕ),(a:ℕ),(i:ℕ),(j:ℕ))))
      · funext y b
        rw [show (data (valuation (values s n p t Y Z)) s (n+1)).2.2.2 y b=
          effectsF (valuation (values s n p t Y Z)) s (n+1) y b from rfl,effectsF_eq]
        suffices factorsZ (valuation (values s n p t Y Z)) s (n+1) y b=Z y b by rw [this]
        ext i j
        simpa [factorsZ,zvar,values,Fin.ofNat_eq_cast] using
          ceval_cvar_valuation (values s n p t Y Z) (.inr (.inr ((y:ℕ),(b:ℕ),(i:ℕ),(j:ℕ))))

theorem truth_sentence (r : RawGame) (hr : ValidRawGame r) (B n k : ℕ)
    (η : ℚ) (a : List (ℤ × ℕ)) :
    Truth (sentence r B n k η a) ↔
      ∃ z : Data r.1 (n+1),Feasible (gameOfRaw r hr) (n+1) η z ∧
        (∑ i,(UpperEntropyPolynomial.polynomial a).eval₂ (algebraMap ℚ ℝ) (z.1 i)) ≤
          (B:ℝ)+1/(n+1:ℝ)+1/(k+1:ℝ) := by
  have hm v : Models v (sentence r B n k η a) ↔
      Feasible (gameOfRaw r hr) (n+1) η (data v r.1 (n+1)) ∧
        (∑ i,(UpperEntropyPolynomial.polynomial a).eval₂ (algebraMap ℚ ℝ)
          ((data v r.1 (n+1)).1 i)) ≤ (B:ℝ)+1/(n+1:ℝ)+1/(k+1:ℝ) := by
    have hE := models_normalization v (r.1.questionsA+1) (r.1.answersA+1) (n+1) (evar (n+1))
    have hF := models_normalization v (r.1.questionsB+1) (r.1.answersB+1) (n+1) (fvar (n+1))
    simp only [sentence,models_append,models_simplex,models_le,eval_rtotal,
      eval_approximation,eval_constant,eval_loss v r hr,
      Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] at *
    change _ ↔ Feasible _ _ _ _ ∧ _
    rw [hE,hF]
    simp only [Feasible,data]
    have hpE := effectsE_pos v r.1 (n+1)
    have hpF := effectsF_pos v r.1 (n+1)
    constructor
    · rintro ⟨⟨⟨⟨⟨hp,hs,ha,ht⟩,hEs⟩,hFs⟩,hl⟩,he⟩
      exact ⟨⟨hp,hs,ha,ht,hpE,hpF,hEs,hFs,hl⟩,he⟩
    · rintro ⟨⟨hp,hs,ha,ht,_,_,hEs,hFs,hl⟩,he⟩
      exact ⟨⟨⟨⟨⟨hp,hs,ha,ht⟩,hEs⟩,hFs⟩,hl⟩,he⟩
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨data v r.1 (n+1),(hm v).mp hv⟩
  · rintro ⟨⟨p,t,E,F⟩,⟨hp,hs,ha,ht,hE,hF,hEs,hFs,hl⟩,he⟩
    choose Y hY using fun x a => (positive_iff_factor (E x a)).mp (hE x a)
    choose Z hZ using fun y b => (positive_iff_factor (F y b)).mp (hF y b)
    have hd := data_valuation r.1 n p t Y Z
    have hY' : (fun x a => (Y x a).conjTranspose*Y x a)=E := by funext x a; exact (hY x a).symm
    have hZ' : (fun y b => (Z y b).conjTranspose*Z y b)=F := by funext y b; exact (hZ y b).symm
    rw [hY',hZ'] at hd
    refine ⟨valuation (values r.1 n p t Y Z),(hm _).mpr ?_⟩
    rw [hd]
    exact ⟨⟨hp,hs,ha,ht,hE,hF,hEs,hFs,hl⟩,he⟩

end Sigma2.UpperEntropySyntax

