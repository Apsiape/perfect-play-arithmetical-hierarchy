import Sigma2.EntropyPolynomialEvaluation

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000
namespace Sigma2.EntropyPolynomial

lemma magnitude_real (N h : ℕ) :
    (magnitude N h : ℝ) = (scale N:ℝ)*
      ∑ i ∈ Finset.range N, ((N.factorial/(i+1):ℕ):ℝ)*((i+1).choose h:ℝ) := by
  have he : magnitude N h = scale N *
      ∑ i ∈ Finset.range N,(N.factorial/(i+1))*(i+1).choose h := by
    unfold magnitude
    rw [sum_map_range]
  rw [he,Nat.cast_mul,Nat.cast_sum]
  simp only [Nat.cast_mul]

lemma numerator_evaluation (N : ℕ) (t : ℝ) :
    (∑ h ∈ Finset.range (N+1),(-1:ℝ)^h*
      (∑ i ∈ Finset.range N,((N.factorial/(i+1):ℕ):ℝ)*((i+1).choose h:ℝ))*t^(h+1)) =
        (N.factorial:ℝ)*EntropySeries.raw N t := by
  calc
    _ = ∑ i ∈ Finset.range N, ((N.factorial/(i+1):ℕ):ℝ)*t*
      (∑ h ∈ Finset.range (N+1),(-1:ℝ)^h*((i+1).choose h:ℝ)*t^h) := by
        simp only [Finset.mul_sum,Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro h hh
        rw [pow_succ]
        ring
    _ = ∑ i ∈ Finset.range N, ((N.factorial/(i+1):ℕ):ℝ)*t*(1-t)^(i+1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [binomial N (i+1) (by have := Finset.mem_range.mp hi; omega)]
    _ = _ := by
      unfold EntropySeries.raw
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [factorial_div_cast N (i+1) (by omega) (by have := Finset.mem_range.mp hi; omega)]
      push_cast
      ring

lemma coefficient_value (N : ℕ) (hN : 0<N) (h : ℕ) :
    ((coefficient N (h+1)).1:ℝ)/((coefficient N (h+1)).2+1) =
      (-1:ℝ)^h*(magnitude N h:ℝ)/(denominator N:ℝ) := by
  have hd := denominator_pos N hN
  simp only [coefficient,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false,
    Nat.add_sub_cancel,signed_real]
  have hh : (denominator N-1:ℕ)+1=denominator N := Nat.sub_add_cancel (by omega)
  rw [← Nat.cast_one,← Nat.cast_add,hh]

lemma finite_coefficient_evaluation (N : ℕ) (hN : 0<N) (t : ℝ) :
    (∑ r ∈ Finset.range (N+2),
      ((coefficient N r).1:ℝ)/((coefficient N r).2+1)*t^r) =
        EntropySeries.raw N t / EntropySeries.logTwoPartial N := by
  rw [show N+2=(N+1)+1 by omega,Finset.sum_range_succ']
  simp only [coefficient_value N hN]
  have hz : ((coefficient N 0).1:ℝ)/((coefficient N 0).2+1)*t^0=0 := by simp [coefficient]
  rw [hz,add_zero]
  simp only [magnitude_real]
  calc
    _ = ((scale N:ℝ)/(denominator N:ℝ))*
        (∑ h ∈ Finset.range (N+1),(-1:ℝ)^h*
          (∑ i ∈ Finset.range N,((N.factorial/(i+1):ℕ):ℝ)*((i+1).choose h:ℝ))*t^(h+1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    _ = ((scale N:ℝ)/(denominator N:ℝ))*((N.factorial:ℝ)*EntropySeries.raw N t) := by
      rw [numerator_evaluation]
    _ = _ := by
      unfold denominator
      rw [Nat.cast_mul,logNumerator_real]
      have hf : (N.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
      have hs : (scale N:ℝ) ≠ 0 := by exact_mod_cast (scale_pos N).ne'
      field_simp

lemma list_coefficient_evaluation (v : ℕ × ℕ) (t : ℝ) :
    (((coefficients v).zipIdx.map (fun qc =>
      ((qc.1.1:ℝ)/(qc.1.2+1))*t^qc.2)).sum) =
        EntropySeries.raw (order v) t / EntropySeries.logTwoPartial (order v) := by
  have he : ((coefficients v).zipIdx.map (fun qc =>
      ((qc.1.1:ℝ)/(qc.1.2+1))*t^qc.2)) =
      List.ofFn (fun i : Fin (order v+2) =>
        ((coefficient (order v) i.val).1:ℝ)/((coefficient (order v) i.val).2+1)*t^i.val) := by
    apply List.ext_getElem
    · simp [coefficients]
    · intro i hi hi'
      simp only [coefficients,List.getElem_map,List.getElem_zipIdx,List.getElem_range,List.getElem_ofFn,Nat.zero_add]
  rw [he,List.sum_ofFn]
  simpa only [Finset.sum_range] using
    finite_coefficient_evaluation (order v) (by unfold order; positivity) t

/-- The identical frozen target, with explicit computable rational coefficients. -/
theorem entropy_polynomial_approximation_proof :
    ∃ coeff : ℕ × ℕ → List (ℤ × ℕ), Computable coeff ∧ ∀ n k, 0 < k →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        |((coeff (n,k)).zipIdx.map (fun qc => ((qc.1.1:ℝ)/(qc.1.2+1))*t^qc.2)).sum-entropyTerm t| ≤
          1/((n+1)*(k:ℝ)) := by
  refine ⟨coefficients,coefficients_primrec.to_comp,?_⟩
  intro n k hk t ht ht1
  rw [list_coefficient_evaluation]
  have hN : 0<order (n,k) := by unfold order; positivity
  have h := EntropySeries.entropy_uniform_error (order (n,k)) hN t ht ht1
  apply h.trans
  have hn : (0:ℝ)<n+1 := by positivity
  have hkr : (0:ℝ)<k := by exact_mod_cast hk
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<order (n,k)+1) (mul_pos hn hkr)).mpr
  unfold order
  push_cast
  nlinarith

#print axioms entropy_polynomial_approximation_proof
end Sigma2.EntropyPolynomial
