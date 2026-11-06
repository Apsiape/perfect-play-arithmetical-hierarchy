import Sigma2.CoarseCells
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.FiniteSpectral
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells

/-- A sharp coarse outcome acts exactly as its finite indicator on every
original positive summand, also when the POVM sums to a support projection. -/
theorem coarse_action {ι τ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq τ]
    (B : ι → Op) (p : ι → τ) (t : τ) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hQ : Projection (coarse B p t)) (a : ι) :
    coarse B p t*B a=if p a=t then B a else 0 := by
  let Q := coarse B p t
  let R := ∑ b,if p b=t then 0 else B b
  have hR : Positive R := by
    apply ContinuousLinearMap.isPositive_sum
    intro b _
    split_ifs
    · exact ContinuousLinearMap.isPositive_zero
    · exact hB b
  change Projection Q at hQ
  have hQR : Q+R=P := by
    dsimp [Q,R,coarse]
    rw [← hs,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  have hPQ : Positive (P-Q) := by rw [← hQR,add_sub_cancel_left]; exact hR
  have hsQ := positive_below_projection Q P (coarse_positive B p t hB) hP hPQ
  have hsBa := positive_below_projection (B a) P (hB a) hP (by
    rw [← hs]; exact positive_sum_erase B hB a)
  by_cases ha : p a=t
  · rw [if_pos ha]
    have hh := positive_below_projection (B a) Q (hB a) hQ (by
      have hpos (b : ι) : Positive (if p b=t then B b else 0) := by
        split_ifs
        · exact hB b
        · exact ContinuousLinearMap.isPositive_zero
      have hh := positive_sum_erase _ hpos a
      simpa only [Q,coarse,ha,ite_true] using hh)
    exact hh.2
  · rw [if_neg ha]
    have hpR : Projection R := by
      have he : R=P-Q := by rw [← hQR]; abel
      rw [he]
      constructor
      · exact (star_sub P Q).trans (congrArg₂ (fun X Y : Op => X-Y) hP.1 hQ.1)
      · rw [sub_mul,mul_sub,mul_sub,hP.2,hsQ.1,hsQ.2,hQ.2]
        abel
    have hh := positive_below_projection (B a) R (hB a) hpR (by
      have hpos (b : ι) : Positive (if p b=t then 0 else B b) := by
        split_ifs
        · exact ContinuousLinearMap.isPositive_zero
        · exact hB b
      have hh := positive_sum_erase _ hpos a
      simpa only [ha,ite_false] using hh)
    have he : R=P-Q := by rw [← hQR]; abel
    rw [he,sub_mul,hsBa.2] at hh
    exact sub_eq_self.mp hh.2

/-- Compress the unchanged POVM to the supplied support, before finite algebra. -/
def compressed {ι : Type} (P : Op) (A : ι → Op) (a : ι) : Op := P*A a*P

theorem compressed_positive {ι : Type} (P : Op) (hP : Projection P)
    (A : ι → Op) (hA : ∀ a,Positive (A a)) (a : ι) : Positive (compressed P A a) := by
  have hh := (hA a).conj_adjoint P
  change Positive (P*A a*star P) at hh
  rw [hP.1] at hh
  exact hh

theorem compressed_sum {ι : Type} [Fintype ι] (P : Op) (hP : Projection P)
    (A : ι → Op) (hs : ∑ a,A a=1) : ∑ a,compressed P A a=P := by
  simp only [compressed,← Finset.sum_mul,← Finset.mul_sum,hs,mul_one,hP.2]

theorem coarse_compressed {ι τ : Type} [Fintype ι] [DecidableEq τ]
    (P : Op) (A : ι → Op) (p : ι → τ) (t : τ) :
    coarse (compressed P A) p t=P*coarse A p t*P := by
  simp only [coarse,compressed,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

/-- The signed value of a cell vanishes on the flag and inactive sectors. -/
def signValue (t : Fin 4) : ℂ := if t=1 then 1 else if t=2 then -1 else 0

def signed {ι : Type} [Fintype ι] (B : ι → Op) (p : ι → Fin 4) : Op :=
  coarse B p 1-coarse B p 2

def weighted {ι : Type} [Fintype ι] (B : ι → Op) (v : ι → ℂ) : Op :=
  ∑ a,v a • B a

theorem signed_eq_weighted {ι : Type} [Fintype ι] (B : ι → Op) (p : ι → Fin 4) :
    signed B p=weighted B (fun a => signValue (p a)) := by
  unfold signed coarse weighted
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  generalize ht : p a=t
  fin_cases t <;> simp [signValue,ht] <;> module

theorem signed_action {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Op) (p : ι → Fin 4) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hQ : ∀ t,Projection (coarse B p t)) (a : ι) :
    signed B p*B a=signValue (p a) • B a := by
  rw [signed,sub_mul,coarse_action B p 1 P hP hB hs (hQ 1),
    coarse_action B p 2 P hP hB hs (hQ 2)]
  generalize ht : p a=t
  fin_cases t <;> simp [signValue,ht] <;> module

theorem signed_weighted {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Op) (p : ι → Fin 4) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hQ : ∀ t,Projection (coarse B p t)) (v : ι → ℂ) :
    signed B p*weighted B v=weighted B (fun a => v a*signValue (p a)) := by
  simp only [weighted,Finset.mul_sum,mul_smul_comm,
    signed_action B p P hP hB hs hQ,smul_smul]

theorem signed_commute {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Op) (p q : ι → Fin 4) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hp : ∀ t,Projection (coarse B p t)) (hq : ∀ t,Projection (coarse B q t)) :
    signed B p*signed B q=signed B q*signed B p := by
  rw [signed_eq_weighted B q,signed_weighted B p P hP hB hs hp,
    ← signed_eq_weighted B q,signed_eq_weighted B p,signed_weighted B q P hP hB hs hq]
  simp only [mul_comm]

def active (B : Fin 6 → Op) : Op := B 1+B 2+B 3+B 4

/-- Products and squares are finite evaluation of the exact published parity table. -/
theorem line_square (B : Fin 6 → Op) (neg : Bool) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hp : ∀ j t,Projection (coarse B (cellClass neg j) t)) (j : Fin 3) :
    signed B (cellClass neg j)*signed B (cellClass neg j)=active B := by
  conv_lhs => rhs; rw [signed_eq_weighted B (cellClass neg j)]
  rw [signed_weighted B (cellClass neg j) P hP hB hs (hp j)]
  cases neg <;> fin_cases j <;>
    norm_num [weighted,active,Fin.sum_univ_succ,cellClass,cellSign,signValue] <;> module

theorem line_product (B : Fin 6 → Op) (neg : Bool) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hp : ∀ j t,Projection (coarse B (cellClass neg j) t)) :
    signed B (cellClass neg 0)*(signed B (cellClass neg 1)*signed B (cellClass neg 2))=
      (if neg then (-1:ℂ) else 1) • active B := by
  rw [signed_eq_weighted B (cellClass neg 2),
    signed_weighted B (cellClass neg 1) P hP hB hs (hp 1),
    signed_weighted B (cellClass neg 0) P hP hB hs (hp 0)]
  cases neg <;>
    norm_num [weighted,active,Fin.sum_univ_succ,cellClass,cellSign,signValue] <;> module

theorem signed_selfadjoint {ι : Type} [Fintype ι] (B : ι → Op) (p : ι → Fin 4)
    (hQ : ∀ t,Projection (coarse B p t)) : star (signed B p)=signed B p := by
  exact (star_sub _ _).trans (congrArg₂ (fun X Y : Op => X-Y) (hQ 1).1 (hQ 2).1)

theorem line_supported (B : Fin 6 → Op) (neg : Bool) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hp : ∀ j t,Projection (coarse B (cellClass neg j) t)) (j : Fin 3) :
    signed B (cellClass neg j)*active B=signed B (cellClass neg j) := by
  rw [active,mul_add,mul_add,mul_add]
  simp only [signed_action B (cellClass neg j) P hP hB hs (hp j)]
  rw [signed_eq_weighted]
  cases neg <;> fin_cases j <;>
    norm_num [weighted,Fin.sum_univ_succ,cellClass,cellSign,signValue] <;> module

#print axioms signed_commute
#print axioms line_product
end Sigma2.FiniteSpectral
