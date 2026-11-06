import Sigma2.ReductionPresentation
import Mathlib.Data.Nat.Prime.Infinite

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace Sigma2.ReductionWitnessArithmetic
open Sigma2.Tree Sigma2.Reduction

/-- Every zero-based prime rank is attained; uses only Euclid and finite counting. -/
theorem exists_primeRank (n : ℕ) : ∃ q, PrimeRank n q := by
  induction n with
  | zero =>
    refine ⟨2,Nat.prime_two,?_⟩
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx,hprime⟩ := Finset.mem_filter.mp hx
    have hxlt := Finset.mem_range.mp hx
    have hxge := hprime.two_le
    omega
  | succ n ih =>
    obtain ⟨q,hq,hcount⟩ := ih
    have hex : ∃ p, q<p ∧ Nat.Prime p := by
      obtain ⟨p,hp,hprime⟩ := Nat.exists_infinite_primes (q+1)
      exact ⟨p,by omega,hprime⟩
    let p := Nat.find hex
    have hp : q<p ∧ Nat.Prime p := Nat.find_spec hex
    have hfilter : (Finset.range p).filter Nat.Prime =
        insert q ((Finset.range q).filter Nat.Prime) := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_insert]
      constructor
      · rintro ⟨hx,hprime⟩
        by_cases hxe : x=q
        · exact Or.inl hxe
        · right
          refine ⟨?_,hprime⟩
          by_contra hn
          have hqx : q<x := by omega
          exact Nat.find_min hex hx ⟨hqx,hprime⟩
      · rintro (rfl | ⟨hx,hprime⟩)
        · exact ⟨hp.1,hq⟩
        · exact ⟨by omega,hprime⟩
    refine ⟨p,hp.2,?_⟩
    rw [hfilter,Finset.card_insert_of_notMem (by simp),hcount]

/-- A genuine Sigma2 witness supplies the prime period and a well separated phase. -/
theorem prime_phase (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e n : ℕ)
    (hn : ∀ t, R (e,n,t)=true) :
    ∃ (q : ℕ) (ζ : ℂ), PrimeRank n q ∧ IsPrimitiveRoot ζ q ∧
      (∀ t, 0<t → ¬q∣t → (1/2:ℝ)^(t+1) ≤ ‖ζ^t-1‖) ∧
      (∀ t x, run (decodeAutomaton (programCode R hR e)) (fun y => decide (q∣y)) t x≠2) := by
  obtain ⟨q,hrank⟩ := exists_primeRank n
  have hq : Nat.Prime q := hrank.1
  obtain ⟨ζ,hζ,hsep⟩ := PrimePhase.good_root q hq
  have hc := (Classical.choose_spec (effective_program R hR)).2 e
  exact ⟨q,ζ,hrank,hζ,hsep,(hc.1 q hq.pos).mpr ⟨n,hrank,hn⟩⟩

/-- The scalar reader is zero on returns and divides the counter off returns. -/
def reader (q : ℕ) (ζ : ℂ) (y : ℕ) : ℂ :=
  if q∣y then 0 else (1/2:ℂ)^(y+1)/(ζ^y-1)

theorem reader_bound (q : ℕ) (ζ : ℂ)
    (hsep : ∀ y, 0<y → ¬q∣y → (1/2:ℝ)^(y+1) ≤ ‖ζ^y-1‖) (y : ℕ) :
    ‖reader q ζ y‖≤1 := by
  by_cases hy : q∣y
  · simp [reader,hy]
  · have hypos : 0<y := Nat.pos_of_ne_zero (fun h => hy (h ▸ dvd_zero q))
    have hlow := hsep y hypos hy
    have hden : 0<‖ζ^y-1‖ := lt_of_lt_of_le (by positivity) hlow
    simp only [reader,if_neg hy]
    have hh : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
    rw [norm_div,norm_pow,hh]
    exact (div_le_one hden).mpr hlow

theorem reader_equation (q : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q) (y : ℕ) :
    reader q ζ y*(ζ^y-1)=(1/2:ℂ)^(y+1)*(if q∣y then 0 else 1) := by
  by_cases hy : q∣y
  · simp [reader,hy]
  · have hne : ζ^y-1≠0 := sub_ne_zero.mpr (fun h => hy ((hζ.pow_eq_one_iff_dvd y).mp h))
    simp [reader,hy,hne]

theorem return_equation (q : ℕ) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q) (y : ℕ) :
    (ζ^y-1)*(if q∣y then (1:ℂ) else 0)=0 := by
  by_cases hy : q∣y
  · simp [hy,(hζ.pow_eq_one_iff_dvd y).mpr hy]
  · simp [hy]

#print axioms exists_primeRank
#print axioms prime_phase
#print axioms reader_bound
#print axioms reader_equation
#print axioms return_equation
end Sigma2.ReductionWitnessArithmetic
