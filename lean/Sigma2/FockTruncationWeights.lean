import Sigma2.FockTruncation

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 400000
namespace Sigma2.FockTruncation
open Sigma2.Tree Sigma2.ReductionFockModel
variable (q : ℕ) [NeZero q]

def mass (m : ℕ) : ℝ := 1-(1/4:ℝ)^(m+1)
def weight (m : ℕ) (u : Index q) : ℝ :=
  if u.1.length ≤ m then ReductionFockWeights.weight q u / mass m else 0

lemma mass_pos (m : ℕ) : 0 < mass m := by
  have h : (1/4:ℝ)^(m+1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  exact sub_pos.mpr h

lemma fiber_hasSum (f : Word → ℝ) (hf : ∀ w, 0 ≤ f w) (a : ℝ) (hs : HasSum f a) :
    HasSum (fun u : Index q => f u.1 / q) a := by
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q)
  have hfin (w : Word) : (∑' i : Fin q, f w / q) = f w := by
    simp only [tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  have hp : Summable (fun u : Index q => f u.1 / q) := by
    apply (summable_prod_of_nonneg (fun u => div_nonneg (hf _) (by positivity))).mpr
    exact ⟨fun w => (hasSum_fintype _).summable,by simpa only [hfin] using hs.summable⟩
  apply hp.hasSum_iff.mpr
  rw [hp.tsum_prod]
  simpa only [hfin] using hs.tsum_eq

lemma cut_weight_hasSum (m : ℕ) :
    HasSum (fun u : Index q => if u.1.length ≤ m then ReductionFockWeights.weight q u else 0) (mass m) := by
  have hn : HasSum (fun n : ℕ => if n ≤ m then (3/4:ℝ)*(1/4:ℝ)^n else 0) (mass m) := by
    have h : HasSum (fun n : ℕ => if n ≤ m then (3/4:ℝ)*(1/4:ℝ)^n else 0)
        (∑ n ∈ Finset.range (m+1), if n ≤ m then (3/4:ℝ)*(1/4:ℝ)^n else 0) :=
      hasSum_sum_of_ne_finset_zero (s := Finset.range (m+1))
      (f := fun n : ℕ => if n ≤ m then (3/4:ℝ)*(1/4:ℝ)^n else 0)
      (fun n hn => by
        have hb : ¬ n ≤ m := by simp only [Finset.mem_range] at hn; omega
        simp [hb])
    convert h using 1
    dsimp [mass]
    rw [Finset.sum_congr rfl (fun n hn => if_pos (by have := Finset.mem_range.mp hn; omega))]
    rw [← Finset.mul_sum,geom_sum_eq (by norm_num : (1/4:ℝ) ≠ 1)]
    ring
  have hw : HasSum (fun w : Word => if w.length ≤ m then fockWeight w else 0) (mass m) := by
    apply FockEntropy.length_hasSum (fun n => if n ≤ m then FockEntropy.probability n else 0)
      (fun n => by split_ifs; exact (FockEntropy.probability_pos n).le; rfl)
    convert hn using 1
    funext n
    split_ifs <;> simp [FockEntropy.weighted_probability]
  have hp := fiber_hasSum q _ (fun w => by split_ifs; exact (FockEntropy.probability_pos w.length).le; rfl) _ hw
  convert hp using 1
  funext u
  split_ifs <;> simp_all [ReductionFockWeights.weight]

lemma weight_nonneg (m : ℕ) (u : Index q) : 0 ≤ weight q m u := by
  unfold weight
  split_ifs
  · exact div_nonneg (ReductionFockWeights.weight_pos q (NeZero.pos q) u).le (mass_pos m).le
  · rfl

lemma weight_hasSum (m : ℕ) : HasSum (weight q m) 1 := by
  have h := (cut_weight_hasSum q m).div_const (mass m)
  convert h using 1
  · funext u
    unfold weight
    split_ifs <;> simp_all
  · exact (div_self (mass_pos m).ne').symm

def probability (m n : ℕ) : ℝ := weight q m ((enumeration q).symm n)
lemma probability_mass (m : ℕ) : HasSum (probability q m) 1 :=
  (enumeration q).symm.hasSum_iff.mpr (weight_hasSum q m)

def density (m : ℕ) : Density := FockModel.diagonalDensity (probability q m)
  (fun n => weight_nonneg q m _) (probability_mass q m).summable (probability_mass q m).tsum_eq

@[simp] lemma density_basis (m : ℕ) (u : Index q) :
    (density q m).op (hilbertBasis q u) = (weight q m u : ℂ) • hilbertBasis q u := by
  rw [hilbertBasis,FockModel.basis_eq]
  change FockModel.diagonal _ _ (Sigma2.basis (enumeration q u)) = _
  ext n
  change (probability q m n : ℂ) * (Sigma2.basis (enumeration q u) n) =
    (weight q m u : ℂ) * (Sigma2.basis (enumeration q u) n)
  by_cases h : n = enumeration q u
  · subst n
    simp only [probability,Equiv.symm_apply_apply]
  · simp [Sigma2.basis,lp.single_apply,h,Ne.symm h]

lemma density_supported (m : ℕ) : cut q m * (density q m).op = (density q m).op := by
  apply ambient_ext q
  intro u
  by_cases h : u.1.length ≤ m <;>
    simp [mul_apply_eq_comp,density_basis,cut_basis,map_smul,weight,h]

lemma density_faithful_on (m : ℕ) (v : H) (hv : cut q m v = v)
    (hz : (density q m).op v = 0) : v = 0 := by
  ext n
  let u := (enumeration q).symm n
  have he : (enumeration q) u = n := (enumeration q).apply_symm_apply n
  have hh := congrArg (fun v : H => v n) hv
  have hd := congrArg (fun v : H => v n) hz
  by_cases h : u.1.length ≤ m
  · have hp : 0 < probability q m n := by
      change 0 < weight q m u
      rw [weight,if_pos h]
      exact div_pos (ReductionFockWeights.weight_pos q (NeZero.pos q) u) (mass_pos m)
    change (probability q m n : ℂ) * v n = 0 at hd
    exact (mul_eq_zero.mp hd).resolve_left (Complex.ofReal_ne_zero.mpr hp.ne')
  · simpa [cut,proj,diag_apply,u,h] using hh.symm

#print axioms weight_hasSum
#print axioms density_faithful_on
end Sigma2.FockTruncation
