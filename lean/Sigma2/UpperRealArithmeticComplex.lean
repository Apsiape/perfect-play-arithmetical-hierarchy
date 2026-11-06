import Sigma2.UpperRealArithmetic
import Mathlib.Analysis.Matrix.Order

namespace Sigma2.UpperRealArithmetic
open scoped BigOperators MatrixOrder ComplexOrder

abbrev CPoly := Poly × Poly

def ceval (v : ℕ → ℝ) (p : CPoly) : ℂ := ⟨eval v p.1, eval v p.2⟩
def czero : CPoly := (constant 0,constant 0)
def cone : CPoly := (constant 1,constant 0)
def cconst (q : ℚ) : CPoly := (constant q,constant 0)
def cvar (n : ℕ) : CPoly := (var (2*n),var (2*n+1))
def cadd (p q : CPoly) : CPoly := (add p.1 q.1,add p.2 q.2)
def csub (p q : CPoly) : CPoly := (sub p.1 q.1,sub p.2 q.2)
def cmul (p q : CPoly) : CPoly :=
  (sub (mul p.1 q.1) (mul p.2 q.2),add (mul p.1 q.2) (mul p.2 q.1))
def cstar (p : CPoly) : CPoly := (p.1,neg p.2)
def csum (ps : List CPoly) : CPoly := (sum (ps.map Prod.fst),sum (ps.map Prod.snd))
def ceq (p q : CPoly) : Sentence := [(true,sub p.1 q.1),(true,sub p.2 q.2)]
def Models (v : ℕ → ℝ) (s : Sentence) : Prop := ∀ a ∈ s, holds v a

@[simp] theorem ceval_zero (v : ℕ → ℝ) : ceval v czero = 0 := by apply Complex.ext <;> simp [ceval,czero]
@[simp] theorem ceval_one (v : ℕ → ℝ) : ceval v cone = 1 := by apply Complex.ext <;> simp [ceval,cone]
@[simp] theorem ceval_const (v : ℕ → ℝ) (q : ℚ) : ceval v (cconst q) = q := by apply Complex.ext <;> simp [ceval,cconst]
@[simp] theorem ceval_add (v : ℕ → ℝ) (p q : CPoly) : ceval v (cadd p q) = ceval v p + ceval v q := by
  apply Complex.ext <;> simp [ceval,cadd]
@[simp] theorem ceval_sub (v : ℕ → ℝ) (p q : CPoly) : ceval v (csub p q) = ceval v p - ceval v q := by
  apply Complex.ext <;> simp [ceval,csub]
@[simp] theorem ceval_mul (v : ℕ → ℝ) (p q : CPoly) : ceval v (cmul p q) = ceval v p * ceval v q := by
  apply Complex.ext <;> simp [ceval,cmul,Complex.mul_re,Complex.mul_im]
@[simp] theorem ceval_star (v : ℕ → ℝ) (p : CPoly) : ceval v (cstar p) = star (ceval v p) := by
  apply Complex.ext <;> simp [ceval,cstar]
@[simp] theorem ceval_sum (v : ℕ → ℝ) (ps : List CPoly) : ceval v (csum ps) = (ps.map (ceval v)).sum := by
  induction ps with
  | nil => apply Complex.ext <;> simp [csum,ceval]
  | cons p ps ih =>
    have : csum (p::ps) = cadd p (csum ps) := rfl
    rw [this,ceval_add,ih]
    simp
@[simp] theorem models_ceq (v : ℕ → ℝ) (p q : CPoly) : Models v (ceq p q) ↔ ceval v p = ceval v q := by
  simp [Models,ceq,holds,sub_eq_zero,Complex.ext_iff,ceval]
@[simp] theorem models_append (v : ℕ → ℝ) (p q : Sentence) : Models v (p++q) ↔ Models v p ∧ Models v q := by
  simp [Models,List.mem_append,or_imp,forall_and]
@[simp] theorem models_flatMap {α : Type*} (v : ℕ → ℝ) (xs : List α) (f : α → Sentence) :
    Models v (xs.flatMap f) ↔ ∀ x ∈ xs, Models v (f x) := by
  constructor
  · intro h x hx a ha; exact h a (List.mem_flatMap.mpr ⟨x,hx,ha⟩)
  · intro h a ha; obtain ⟨x,hx,ha⟩ := List.mem_flatMap.mp ha; exact h x hx a ha

/-- Exact factor certificate, for every finite complex matrix, including size zero. -/
theorem positive_iff_factor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : Matrix ι ι ℂ) : X.PosSemidef ↔ ∃ Y : Matrix ι ι ℂ, X = Y.conjTranspose * Y := by
  exact Matrix.nonneg_iff_posSemidef.symm.trans CStarAlgebra.nonneg_iff_eq_star_mul_self

end Sigma2.UpperRealArithmetic

