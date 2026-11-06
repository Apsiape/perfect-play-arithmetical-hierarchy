import Sigma2.UpperRealArithmeticMatrix

/-! Explicit polynomial constraints for the finite Schmidt stage.
All positivity certificates are finite complex Gram factors. -/
namespace Sigma2.UpperStageSyntax
open Sigma2.UpperRealArithmetic
open scoped BigOperators ComplexOrder

abbrev Label := ℕ ⊕ ((ℕ × ℕ × ℕ × ℕ) ⊕ (ℕ × ℕ × ℕ × ℕ))

def dvar (i : ℕ) : Poly := var (2 * Encodable.encode (Sum.inl i : Label))
def yvar (x a i j : ℕ) : CPoly :=
  cvar (Encodable.encode (Sum.inr (Sum.inl (x,a,i,j)) : Label))
def zvar (y b i j : ℕ) : CPoly :=
  cvar (Encodable.encode (Sum.inr (Sum.inr (y,b,i,j)) : Label))

def bounded (n : ℕ) (f : ℕ → Sentence) : Sentence := (List.range n).flatMap f
def rtotal (n : ℕ) (f : ℕ → Poly) : Poly := sum ((List.range n).map f)
def ctotal (n : ℕ) (f : ℕ → CPoly) : CPoly := csum ((List.range n).map f)
def eq (p q : Poly) : Sentence := [(true,sub p q)]
def le (p q : Poly) : Sentence := [(false,sub q p)]
def normSq (p : CPoly) : Poly := add (mul p.1 p.1) (mul p.2 p.2)
def gramN (m : ℕ) (Y : ℕ → ℕ → CPoly) (i j : ℕ) : CPoly :=
  ctotal m fun k => cmul (cstar (Y k i)) (Y k j)
def evar (m x a i j : ℕ) : CPoly := gramN m (yvar x a) i j
def fvar (m y b i j : ℕ) : CPoly := gramN m (zvar y b) i j

def sandwich (m x y a b i j : ℕ) : CPoly :=
  ctotal m fun k => cmul (cmul (evar m x a i k) (dvar k,constant 0)) (fvar m y b j k)

def amplitudeConstraints (κ m : ℕ) : Sentence :=
  eq (dvar 0) (constant 1) ++
  bounded m (fun i => le (constant 0) (dvar i)) ++
  bounded m (fun i => bounded m fun j => if i ≤ j then le (dvar j) (dvar i) else []) ++
  le (rtotal m fun i => mul (dvar i) (dvar i)) (constant κ)

def normalization (q a m : ℕ) (V : ℕ → ℕ → ℕ → ℕ → CPoly) : Sentence :=
  bounded q fun x => bounded m fun i => bounded m fun j =>
    ceq (ctotal a fun b => V x b i j) (if i = j then cone else czero)

def losingConstraints (q r a b m : ℕ) (L : ℕ → ℕ → ℕ → ℕ → Bool) (ε : ℚ) : Sentence :=
  bounded q fun x => bounded r fun y => bounded a fun u => bounded b fun v =>
    if L x y u v then bounded m fun i => bounded m fun j =>
      le (normSq (sandwich m x y u v i j)) (constant ε) else []

def sentence (s : Scenario) (κ n : ℕ) (L : ℕ → ℕ → ℕ → ℕ → Bool) : Sentence :=
  amplitudeConstraints κ (n+1) ++
  normalization (s.questionsA+1) (s.answersA+1) (n+1) (evar (n+1)) ++
  normalization (s.questionsB+1) (s.answersB+1) (n+1) (fvar (n+1)) ++
  losingConstraints (s.questionsA+1) (s.questionsB+1) (s.answersA+1) (s.answersB+1)
    (n+1) L ((κ:ℚ)/(n+2))

@[simp] theorem models_eq (v : ℕ → ℝ) (p q : Poly) :
    Models v (eq p q) ↔ eval v p = eval v q := by simp [eq,Models,holds,sub_eq_zero]
@[simp] theorem models_le (v : ℕ → ℝ) (p q : Poly) :
    Models v (le p q) ↔ eval v p ≤ eval v q := by simp [le,Models,holds,sub_nonneg]
@[simp] theorem models_bounded (v : ℕ → ℝ) (n : ℕ) (f : ℕ → Sentence) :
    Models v (bounded n f) ↔ ∀ i : Fin n, Models v (f i) := by
  simp only [bounded,models_flatMap,List.mem_range]
  exact ⟨fun h i => h i i.isLt, fun h i hi => h ⟨i,hi⟩⟩

theorem sum_range_fin {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simpa [List.range_succ,Fin.sum_univ_castSucc] using congrArg (· + f n) ih
@[simp] theorem eval_rtotal (v : ℕ → ℝ) (n : ℕ) (f : ℕ → Poly) :
    eval v (rtotal n f) = ∑ i : Fin n, eval v (f i) := by
  simp only [rtotal,eval_sum,List.map_map,Function.comp_def,sum_range_fin]
@[simp] theorem ceval_ctotal (v : ℕ → ℝ) (n : ℕ) (f : ℕ → CPoly) :
    ceval v (ctotal n f) = ∑ i : Fin n, ceval v (f i) := by
  simp only [ctotal,ceval_sum,List.map_map,Function.comp_def,sum_range_fin]
@[simp] theorem eval_normSq (v : ℕ → ℝ) (p : CPoly) :
    eval v (normSq p) = ‖ceval v p‖^2 := by
  simp only [normSq,eval_add,eval_mul,Complex.sq_norm,Complex.normSq_apply,ceval]

noncomputable def amplitudes (v : ℕ → ℝ) (m : ℕ) : Fin m → ℝ := fun i => eval v (dvar i)
noncomputable def factorsY (v : ℕ → ℝ) (s : Scenario) (m : ℕ)
    (x : QA s) (a : AA s) : Matrix (Fin m) (Fin m) ℂ := fun i j => ceval v (yvar x a i j)
noncomputable def factorsZ (v : ℕ → ℝ) (s : Scenario) (m : ℕ)
    (y : QB s) (b : BB s) : Matrix (Fin m) (Fin m) ℂ := fun i j => ceval v (zvar y b i j)
noncomputable def effectsE (v : ℕ → ℝ) (s : Scenario) (m : ℕ)
    (x : QA s) (a : AA s) : Matrix (Fin m) (Fin m) ℂ := fun i j => ceval v (evar m x a i j)
noncomputable def effectsF (v : ℕ → ℝ) (s : Scenario) (m : ℕ)
    (y : QB s) (b : BB s) : Matrix (Fin m) (Fin m) ℂ := fun i j => ceval v (fvar m y b i j)

@[simp] theorem effectsE_eq (v : ℕ → ℝ) (s : Scenario) (m : ℕ) (x : QA s) (a : AA s) :
    effectsE v s m x a = (factorsY v s m x a).conjTranspose * factorsY v s m x a := by
  ext i j
  simp [effectsE,factorsY,evar,gramN,Matrix.mul_apply,Matrix.conjTranspose_apply]
@[simp] theorem effectsF_eq (v : ℕ → ℝ) (s : Scenario) (m : ℕ) (y : QB s) (b : BB s) :
    effectsF v s m y b = (factorsZ v s m y b).conjTranspose * factorsZ v s m y b := by
  ext i j
  simp [effectsF,factorsZ,fvar,gramN,Matrix.mul_apply,Matrix.conjTranspose_apply]

theorem effectsE_pos (v : ℕ → ℝ) (s : Scenario) (m : ℕ) (x : QA s) (a : AA s) :
    (effectsE v s m x a).PosSemidef :=
  (positive_iff_factor _).mpr ⟨factorsY v s m x a,effectsE_eq v s m x a⟩
theorem effectsF_pos (v : ℕ → ℝ) (s : Scenario) (m : ℕ) (y : QB s) (b : BB s) :
    (effectsF v s m y b).PosSemidef :=
  (positive_iff_factor _).mpr ⟨factorsZ v s m y b,effectsF_eq v s m y b⟩

theorem ceval_sandwich (v : ℕ → ℝ) (s : Scenario) (m : ℕ)
    (x : QA s) (y : QB s) (a : AA s) (b : BB s) (i j : Fin m) :
    ceval v (sandwich m x y a b i j) =
      (effectsE v s m x a * Matrix.diagonal (fun k => (amplitudes v m k : ℂ)) *
        (effectsF v s m y b).transpose) i j := by
  rw [sandwich,ceval_ctotal,Matrix.mul_apply]
  simp only [ceval_mul,Matrix.mul_diagonal,Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro k _
  change ceval v (evar m x a i k) * ceval v (dvar k,constant 0) * ceval v (fvar m y b j k) = _
  have hd : ceval v (dvar k,constant 0) = (amplitudes v m k : ℂ) := by
    apply Complex.ext <;> simp [ceval,amplitudes]
  rw [hd]
  rfl
theorem models_amplitude (v : ℕ → ℝ) (κ n : ℕ) :
    Models v (amplitudeConstraints κ (n+1)) ↔
      amplitudes v (n+1) 0 = 1 ∧ (∀ i, 0 ≤ amplitudes v (n+1) i) ∧
      Antitone (amplitudes v (n+1)) ∧ (∑ i, amplitudes v (n+1) i ^ 2) ≤ κ := by
  simp only [amplitudeConstraints,models_append,models_eq,models_le,models_bounded,
    eval_constant,eval_rtotal,eval_mul]
  have hi : (∀ i j : Fin (n+1), Models v (if (i:ℕ) ≤ j then le (dvar j) (dvar i) else [])) ↔
      Antitone (amplitudes v (n+1)) := by
    constructor
    · intro h i j hij
      have hh := h i j
      rw [if_pos (show (i:ℕ) ≤ j from hij),models_le] at hh
      exact hh
    · intro h i j
      split_ifs with hij
      · exact (models_le _ _ _).mpr (h hij)
      · simp [Models]
  rw [hi]
  simp only [Rat.cast_zero,Rat.cast_one,Rat.cast_natCast,amplitudes,pow_two,Fin.val_zero]
  tauto

end Sigma2.UpperStageSyntax