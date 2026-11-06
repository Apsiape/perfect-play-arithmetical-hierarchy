import Sigma2.Statements
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

noncomputable section
open scoped BigOperators
namespace Sigma2.EntropyDomination

lemma entropy_nonneg {p : ℝ} (h0 : 0≤p) (h1 : p≤1) : 0≤entropyTerm p := by
  exact div_nonneg (Real.negMulLog_nonneg h0 h1) (le_of_lt (Real.log_pos (by norm_num : (1:ℝ)<2)))

/-- An entropy bound for an entry dominated by a fixed multiple of a reference
entry; no monotonicity of entropy on the whole unit interval is needed. -/
lemma entropy_le {p q c : ℝ} (hp0 : 0≤p) (hp1 : p≤1) (hq0 : 0≤q)
    (hc : 0≤c) (hqp : q≤c*p) :
    entropyTerm q≤c*entropyTerm p+p/Real.log 2 := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  by_cases hp : p=0
  · have hq : q=0 := by rw [hp,mul_zero] at hqp; linarith
    simp [hp,hq,entropyTerm]
  have hpp : 0<p := lt_of_le_of_ne hp0 (Ne.symm hp)
  let r := q/p
  have hr : 0≤r := div_nonneg hq0 hp0
  have hrc : r≤c := (div_le_iff₀ hpp).mpr hqp
  have hq : p*r=q := by dsimp [r]; field_simp
  have hn : 0≤Real.negMulLog p := Real.negMulLog_nonneg hp0 hp1
  have hb : Real.negMulLog r≤1 := (Real.negMulLog_le_one_sub_self hr).trans (by linarith)
  have he : Real.negMulLog q≤c*Real.negMulLog p+p := by
    rw [← hq,Real.negMulLog_mul]
    nlinarith [mul_le_mul_of_nonneg_right hrc hn,mul_le_mul_of_nonneg_left hb hp0]
  change Real.negMulLog q/Real.log 2≤c*(Real.negMulLog p/Real.log 2)+p/Real.log 2
  calc
    _ ≤ (c*Real.negMulLog p+p)/Real.log 2 := (div_le_div_iff_of_pos_right hlog).mpr he
    _ = _ := by ring

/-- Pointwise spectral domination is sufficient for finite entropy. This lemma
also applies after separately constructing a common eigenvalue ordering. -/
theorem summable_entropy_of_le (p q : ℕ → ℝ) (c : ℝ)
    (hp0 : ∀ i,0≤p i) (hp1 : ∀ i,p i≤1) (hq0 : ∀ i,0≤q i)
    (hq1 : ∀ i,q i≤1) (hc : 0≤c) (hqp : ∀ i,q i≤c*p i)
    (hs : Summable p) (hh : Summable (fun i => entropyTerm (p i))) :
    Summable (fun i => entropyTerm (q i)) := by
  apply Summable.of_nonneg_of_le (fun i => entropy_nonneg (hq0 i) (hq1 i))
    (fun i => entropy_le (hp0 i) (hp1 i) (hq0 i) hc (hqp i))
    ((hh.mul_left c).add (hs.div_const (Real.log 2)))

#print axioms summable_entropy_of_le
end Sigma2.EntropyDomination
