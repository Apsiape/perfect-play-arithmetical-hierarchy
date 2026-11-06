import Sigma2.ReductionPresentation

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 300000
set_option pp.proofs false
namespace Sigma2.ReductionFockWeights
open Sigma2.Tree

def weight (q : ℕ) (u : Word × Fin q) : ℝ := fockWeight u.1/q

theorem weight_pos (q : ℕ) (hq : 0<q) (u : Word × Fin q) : 0<weight q u := by
  unfold weight fockWeight
  positivity

theorem fiber_mass (q : ℕ) (hq : 0<q) (w : Word) :
    (∑' i : Fin q, weight q (w,i))=fockWeight w := by
  simp only [weight,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  field_simp

theorem mass (q : ℕ) (hq : 0<q) :
    Summable (weight q) ∧ (∑' u,weight q u)=1 := by
  have hs : Summable (weight q) :=
    (summable_prod_of_nonneg (fun u => (weight_pos q hq u).le)).mpr
      ⟨fun w => (hasSum_fintype _).summable,by simpa only [fiber_mass q hq] using fock_entropy.1⟩
  refine ⟨hs,?_⟩
  rw [hs.tsum_prod]
  simpa only [fiber_mass q hq] using fock_entropy.2.1

theorem entropy_formula (q : ℕ) (hq : 0<q) (w : Word) (i : Fin q) :
    entropyTerm (weight q (w,i))=entropyTerm (fockWeight w)/q+
      (fockWeight w/q)*(Real.log q/Real.log 2) := by
  have hw : 0<fockWeight w := by unfold fockWeight; positivity
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  simp only [weight,entropyTerm]
  rw [Real.log_div hw.ne' hqR]
  ring

theorem entropy_fiber (q : ℕ) (hq : 0<q) (w : Word) :
    (∑' i : Fin q,entropyTerm (weight q (w,i)))=
      entropyTerm (fockWeight w)+fockWeight w*(Real.log q/Real.log 2) := by
  simp only [entropy_formula q hq,tsum_fintype,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hqR : (q : ℝ)≠0 := by exact_mod_cast hq.ne'
  field_simp
  <;> ring

theorem entropy (q : ℕ) (hq : 0<q) :
    Summable (fun u => entropyTerm (weight q u)) ∧
      (∑' u,entropyTerm (weight q u))=
        Real.log (4/3)/Real.log 2+4/3+Real.log q/Real.log 2 := by
  have hqR : (1 : ℝ)≤q := by exact_mod_cast hq
  have hc : 0≤Real.log q/Real.log 2 :=
    div_nonneg (Real.log_nonneg hqR) (le_of_lt (Real.log_pos (by norm_num)))
  have hp (w : Word) : 0≤entropyTerm (fockWeight w) := by
    change 0≤entropyTerm (FockEntropy.probability w.length)
    rw [FockEntropy.entropy_formula]
    exact mul_nonneg (FockEntropy.probability_pos _).le
      (add_nonneg FockEntropy.offset_nonneg (by positivity))
  have hnonneg (u : Word × Fin q) : 0≤entropyTerm (weight q u) := by
    rw [entropy_formula q hq u.1 u.2]
    exact add_nonneg (div_nonneg (hp _) (by positivity))
      (mul_nonneg (by unfold fockWeight; positivity) hc)
  have hw := fock_entropy.1.mul_right (Real.log q/Real.log 2)
  have hs : Summable (fun u => entropyTerm (weight q u)) :=
    (summable_prod_of_nonneg hnonneg).mpr ⟨fun w => (hasSum_fintype _).summable,
      by simpa only [entropy_fiber q hq] using fock_entropy.2.2.1.add hw⟩
  refine ⟨hs,?_⟩
  rw [hs.tsum_prod]
  simp_rw [entropy_fiber q hq]
  rw [fock_entropy.2.2.1.tsum_add hw,tsum_mul_right,fock_entropy.2.2.2,fock_entropy.2.1,one_mul]

#print axioms mass
#print axioms entropy
end Sigma2.ReductionFockWeights
