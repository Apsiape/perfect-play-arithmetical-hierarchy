import Sigma2.Statements
import Mathlib.Data.List.OfFn
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open scoped BigOperators
namespace Sigma2.FockEntropy

/-- Group the absolutely nonnegative word sum by its actual finite length. -/
theorem length_hasSum (f : ℕ → ℝ) (hf : ∀ n,0 ≤ f n) (a : ℝ)
    (hs : HasSum (fun n => (4:ℝ)^n*f n) a) :
    HasSum (fun w : List (Fin 4) => f w.length) a := by
  let F : (Σ n : ℕ,Fin n → Fin 4) → ℝ := fun x => f x.1
  have hfin (n : ℕ) : (∑' _ : Fin n → Fin 4,f n)=(4:ℝ)^n*f n := by
    simp [F,Fintype.card_fun]
  have hF : Summable F := by
    apply (summable_sigma_of_nonneg (fun x => hf x.1)).mpr
    refine ⟨fun n => (hasSum_fintype _).summable,?_⟩
    simpa only [F,hfin] using hs.summable
  have hsum : HasSum F a := by
    apply hF.hasSum_iff.mpr
    rw [hF.tsum_sigma]
    simpa only [F,hfin] using hs.tsum_eq
  exact (List.equivSigmaTuple.hasSum_iff).mpr hsum

def probability (n : ℕ) : ℝ := (3/4:ℝ)*(1/16:ℝ)^n

def weight (w : List (Fin 4)) : ℝ := probability w.length

def offset : ℝ := Real.log (4/3)/Real.log 2

theorem probability_pos (n : ℕ) : 0<probability n := by unfold probability; positivity

theorem offset_nonneg : 0 ≤ offset := by
  unfold offset
  exact div_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by norm_num))

theorem entropy_formula (n : ℕ) :
    entropyTerm (probability n)=probability n*(offset+4*(n:ℝ)) := by
  have hl0 : Real.log (3/4:ℝ)=-Real.log (4/3:ℝ) := by
    rw [show (3/4:ℝ)=(4/3:ℝ)⁻¹ by norm_num,Real.log_inv]
  have hl1 : Real.log (1/16:ℝ)=-4*Real.log 2 := by
    rw [show (1/16:ℝ)=(2^4:ℝ)⁻¹ by norm_num,Real.log_inv,Real.log_pow]
    ring
  have hn : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold entropyTerm probability offset
  rw [Real.log_mul (by norm_num : (3/4:ℝ)≠0)
    (pow_ne_zero n (by norm_num : (1/16:ℝ)≠0)),Real.log_pow,hl0,hl1]
  field_simp [hn]
  <;> ring

theorem weighted_probability (n : ℕ) :
    (4:ℝ)^n*probability n=(3/4:ℝ)*(1/4:ℝ)^n := by
  unfold probability
  calc
    _ = (3/4:ℝ)*((4:ℝ)^n*(1/16:ℝ)^n) := by ring
    _ = _ := by rw [← mul_pow]; norm_num

theorem weighted_entropy (n : ℕ) :
    (4:ℝ)^n*entropyTerm (probability n)=
      (offset*(3/4:ℝ))*(1/4:ℝ)^n+3*((n:ℝ)*(1/4:ℝ)^n) := by
  rw [entropy_formula,← mul_assoc,weighted_probability]
  ring

/-- The original Fock law, with its exact spectral entropy-term sum. -/
theorem result : Summable weight ∧ (∑' w,weight w)=1 ∧
    Summable (fun w => entropyTerm (weight w)) ∧
    (∑' w,entropyTerm (weight w))=Real.log (4/3)/Real.log 2+4/3 := by
  have hg : HasSum (fun n : ℕ => (1/4:ℝ)^n) (4/3:ℝ) := by
    convert hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖<1) using 1 <;> norm_num
  have hn : HasSum (fun n : ℕ => (n:ℝ)*(1/4:ℝ)^n) (4/9:ℝ) := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/4:ℝ)‖<1) using 1 <;> norm_num
  have hp : HasSum weight 1 := by
    apply length_hasSum probability (fun n => (probability_pos n).le)
    have hh := hg.mul_left (3/4:ℝ)
    convert hh using 1
    · funext n
      exact weighted_probability n
    · norm_num
  have hent_nonneg (n : ℕ) : 0 ≤ entropyTerm (probability n) := by
    rw [entropy_formula]
    exact mul_nonneg (probability_pos n).le (add_nonneg offset_nonneg (by positivity))
  have he : HasSum (fun w => entropyTerm (weight w)) (offset+4/3) := by
    apply length_hasSum (fun n => entropyTerm (probability n)) hent_nonneg
    have hh := (hg.mul_left (offset*(3/4:ℝ))).add (hn.mul_left 3)
    convert hh using 1
    · funext n
      exact weighted_entropy n
    · ring
  exact ⟨hp.summable,hp.tsum_eq,he.summable,he.tsum_eq⟩

#print axioms result
end Sigma2.FockEntropy
