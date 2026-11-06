import Sigma2.UpperEntropySlack

noncomputable section
open scoped BigOperators
namespace Sigma2.UpperEntropyPolynomial

/-- The exact rational polynomial represented by the clock development's coefficient list. -/
def polynomial (a : List (ℤ × ℕ)) : Polynomial ℚ :=
  (a.zipIdx.map fun qc => Polynomial.C ((qc.1.1:ℚ)/(qc.1.2+1))*Polynomial.X^qc.2).sum

@[simp] theorem eval_polynomial (a : List (ℤ × ℕ)) (t : ℝ) :
    (polynomial a).eval₂ (algebraMap ℚ ℝ) t=
      (a.zipIdx.map (fun qc => ((qc.1.1:ℝ)/(qc.1.2+1))*t^qc.2)).sum := by
  simp [polynomial,Polynomial.eval₂_list_sum,List.map_map,Function.comp_def]

/-- Pointwise uniform error at dimension n+1 gives the total finite entropy error. -/
theorem finite_approximation (coeff : ℕ × ℕ → List (ℤ × ℕ))
    (hc : ∀ n k,0 < k → ∀ t : ℝ,0 ≤ t → t ≤ 1 →
      |((coeff (n,k)).zipIdx.map
        (fun qc => ((qc.1.1:ℝ)/(qc.1.2+1))*t^qc.2)).sum-entropyTerm t| ≤
          1/((n+1)*(k:ℝ)))
    (n k : ℕ) (p : Fin (n+1) → ℝ) (hp : ∀ i,0 ≤ p i) (hs : (∑ i,p i)=1) :
    |(∑ i,(polynomial (coeff (n,k+1))).eval₂ (algebraMap ℚ ℝ) (p i))-
      (∑ i,entropyTerm (p i))| ≤ 1/(k+1:ℝ) := by
  have hp1 i : p i ≤ 1 :=
    (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)).trans_eq hs
  have he i : |(polynomial (coeff (n,k+1))).eval₂ (algebraMap ℚ ℝ) (p i)-
      entropyTerm (p i)| ≤ 1/((n+1:ℝ)*(k+1:ℝ)) := by
    simpa only [eval_polynomial,Nat.cast_add,Nat.cast_one] using
      hc n (k+1) (Nat.succ_pos k) (p i) (hp i) (hp1 i)
  calc
    _ = |∑ i,((polynomial (coeff (n,k+1))).eval₂ (algebraMap ℚ ℝ) (p i)-
        entropyTerm (p i))| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i,|(polynomial (coeff (n,k+1))).eval₂ (algebraMap ℚ ℝ) (p i)-
        entropyTerm (p i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (n+1),1/((n+1:ℝ)*(k+1:ℝ)) :=
      Finset.sum_le_sum fun i _ => he i
    _ = 1/(k+1:ℝ) := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Nat.cast_add,Nat.cast_one]
      field_simp

end Sigma2.UpperEntropyPolynomial
