import Sigma2.PresentationCoding
import Sigma2.EntropySeries
import Mathlib.Data.Nat.Choose.Factorization

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000
namespace Sigma2.EntropyPolynomial

/-- Common denominator for the finite logarithm series at 1/2. -/
def scale (N : ℕ) : ℕ := N.factorial * 2^N

def logNumerator (N : ℕ) : ℕ :=
  ((List.range N).map (fun i => (N.factorial/(i+1))*2^(N-(i+1)))).sum

def magnitude (N h : ℕ) : ℕ := scale N *
  ((List.range N).map (fun i => (N.factorial/(i+1))*(i+1).choose h)).sum

def signed (h a : ℕ) : ℤ := if h%2=0 then (a:ℤ) else -(a:ℤ)
def denominator (N : ℕ) : ℕ := N.factorial * logNumerator N

def coefficient (N r : ℕ) : ℤ × ℕ :=
  (if r=0 then 0 else signed (r-1) (magnitude N (r-1)),denominator N-1)

def order (v : ℕ × ℕ) : ℕ := 10*(v.1+1)*(v.2+1)
def coefficients (v : ℕ × ℕ) : List (ℤ × ℕ) :=
  (List.range (order v+2)).map (coefficient (order v))

open Sigma2.SimulatorPrimrec Sigma2.PresentationCoding
variable {α : Type} [Primcodable α]

lemma nat_pow_primrec : Primrec₂ ((·^·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow
@[fun_prop] lemma ppow (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a ^ g a) := nat_pow_primrec.comp hf hg

lemma factorial_primrec : Primrec Nat.factorial := by
  have h := Primrec.nat_rec₁ (1:ℕ)
    (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst) Primrec.snd).to₂
  exact h.of_eq (fun n => by induction n <;> simp [Nat.factorial_succ, *])
@[fun_prop] lemma pfactorial (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun a => (f a).factorial) := factorial_primrec.comp hf

lemma sum_primrec : Primrec (List.sum : List ℕ → ℕ) := by
  have hh : Primrec (fun z : List ℕ × (ℕ × ℕ) => z.2.1+z.2.2) := by fun_prop
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0) hh.to₂).of_eq (fun l => by induction l <;> simp_all)
@[fun_prop] lemma psum (f : α → List ℕ) (hf : Primrec f) :
    Primrec (fun a => (f a).sum) := sum_primrec.comp hf

lemma choose_primrec : Primrec₂ Nat.choose := by
  have h : Primrec (fun v : ℕ × ℕ => if v.2 ≤ v.1 then
      v.1.factorial/(v.2.factorial*(v.1-v.2).factorial) else 0) := by
    apply Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst) <;> fun_prop
  apply h.of_eq
  intro v
  by_cases hv : v.2 ≤ v.1
  · simp only [hv,ite_true]
    exact (Nat.choose_eq_factorial_div_factorial hv).symm
  · simp [hv,Nat.choose_eq_zero_of_lt (by omega : v.1<v.2)]
@[fun_prop] lemma pchoose (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).choose (g a)) := choose_primrec.comp hf hg

lemma encode_ofNat (n : ℕ) : Encodable.encode (n:ℤ)=2*n := by rfl
lemma encode_neg_ofNat (n : ℕ) :
    Encodable.encode (-(n:ℤ))=if n=0 then 0 else 2*n-1 := by
  cases n with
  | zero => rfl
  | succ n => change 2*n+1=2*(n+1)-1; omega

@[fun_prop] lemma pofNat (f : α → ℕ) (hf : Primrec f) : Primrec (fun a => (f a : ℤ)) := by
  apply Primrec.encode_iff.mp
  simp only [encode_ofNat]
  fun_prop
@[fun_prop] lemma pnegOfNat (f : α → ℕ) (hf : Primrec f) : Primrec (fun a => -(f a : ℤ)) := by
  apply Primrec.encode_iff.mp
  simp only [encode_neg_ofNat]
  fun_prop
@[fun_prop] lemma psigned (h f : α → ℕ) (hh : Primrec h) (hf : Primrec f) :
    Primrec (fun a => signed (h a) (f a)) := by
  unfold signed
  fun_prop

@[fun_prop] lemma pscale (f : α → ℕ) (hf : Primrec f) : Primrec (fun a => scale (f a)) := by
  unfold scale
  fun_prop
@[fun_prop] lemma plogNumerator (f : α → ℕ) (hf : Primrec f) : Primrec (fun a => logNumerator (f a)) := by
  unfold logNumerator
  apply psum
  apply Primrec.list_map
  · fun_prop
  · have h : Primrec (fun z : α × ℕ => (f z.1).factorial/(z.2+1)*2^(f z.1-(z.2+1))) := by fun_prop
    exact h.to₂
@[fun_prop] lemma pmagnitude (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => magnitude (f a) (g a)) := by
  unfold magnitude
  apply pmul
  · fun_prop
  · apply psum
    apply Primrec.list_map
    · fun_prop
    · have h : Primrec (fun z : α × ℕ => (f z.1).factorial/(z.2+1)*(z.2+1).choose (g z.1)) := by fun_prop
      exact h.to₂
@[fun_prop] lemma pdenominator (f : α → ℕ) (hf : Primrec f) : Primrec (fun a => denominator (f a)) := by
  unfold denominator
  fun_prop
@[fun_prop] lemma pcoefficient (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => coefficient (f a) (g a)) := by
  unfold coefficient
  fun_prop

lemma coefficients_primrec : Primrec coefficients := by
  unfold coefficients
  apply Primrec.list_map
  · unfold order; fun_prop
  · have h : Primrec (fun z : (ℕ × ℕ) × ℕ => coefficient (order z.1) z.2) := by
      apply pcoefficient
      · unfold order; fun_prop
      · fun_prop
    exact h.to₂

#print axioms coefficients_primrec
end Sigma2.EntropyPolynomial
