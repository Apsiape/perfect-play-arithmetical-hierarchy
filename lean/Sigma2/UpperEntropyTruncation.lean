import Sigma2.UpperEntropyFinite
import Sigma2.UpperEntropyCompact
import Sigma2.UpperEffective

noncomputable section
open scoped BigOperators
namespace Sigma2.UpperEntropyTruncation
open UpperFiniteBorn UpperFiniteAmplitudes

def mass (p : ℕ → ℝ) (m : ℕ) : ℝ := ∑ i : Fin m,p i

def probabilities (p : ℕ → ℝ) (m : ℕ) : Fin m → ℝ := fun i => p i/mass p m

theorem mass_le_one (p : ℕ → ℝ) (hp : ∀ i,0 ≤ p i) (hs : Summable p)
    (ht : (∑' i,p i)=1) (m : ℕ) : mass p m ≤ 1 := by
  unfold mass
  rw [Fin.sum_univ_eq_sum_range]
  exact (hs.sum_le_tsum _ (fun i _ => hp i)).trans_eq ht

theorem normalized_simplex (p : ℕ → ℝ) (hp : ∀ i,0 ≤ p i) (ha : Antitone p)
    (m : ℕ) (hm : 0 < mass p m) :
    (∀ i,0 ≤ probabilities p m i) ∧ (∑ i,probabilities p m i)=1 ∧
      Antitone (probabilities p m) := by
  refine ⟨fun i => div_nonneg (hp i) hm.le,?_,?_⟩
  · simp only [probabilities,← Finset.sum_div]
    exact div_self (ne_of_gt hm)
  · intro i j hij
    exact div_le_div_of_nonneg_right (ha hij) hm.le

/-- Normalized truncation has a true entropy estimate; no polynomial oracle is used. -/
theorem entropy_bound (p : ℕ → ℝ) (hp : ∀ i,0 ≤ p i) (hs : Summable p)
    (ht : (∑' i,p i)=1) (hH : Summable (fun i => entropyTerm (p i)))
    (m : ℕ) (hm : 1/2 ≤ mass p m) :
    (∑ i,entropyTerm (probabilities p m i)) ≤
      2*(∑' i,entropyTerm (p i))+1/Real.log 2 := by
  have hp1 i : p i ≤ 1 := (hs.le_tsum i (fun j _ => hp j)).trans_eq ht
  have hpos : 0 < mass p m := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 ≤ 1/mass p m := by positivity
  have hc2 : 1/mass p m ≤ 2 := (div_le_iff₀ hpos).mpr (by linarith)
  have he i : entropyTerm (probabilities p m i) ≤
      (1/mass p m)*entropyTerm (p i)+p i/Real.log 2 := by
    apply EntropyDomination.entropy_le (hp i) (hp1 i) (div_nonneg (hp i) hpos.le) hc
    change p i/mass p m ≤ (1/mass p m)*p i
    exact le_of_eq (by ring)
  have hsumH0 : 0 ≤ ∑ i : Fin m,entropyTerm (p i) :=
    Finset.sum_nonneg fun i _ => EntropyDomination.entropy_nonneg (hp i) (hp1 i)
  have hsumH : (∑ i : Fin m,entropyTerm (p i)) ≤ ∑' i,entropyTerm (p i) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => entropyTerm (p i)) m]
    exact hH.sum_le_tsum _ (fun i _ => EntropyDomination.entropy_nonneg (hp i) (hp1 i))
  calc
    _ ≤ ∑ i : Fin m,((1/mass p m)*entropyTerm (p i)+p i/Real.log 2) :=
      Finset.sum_le_sum fun i _ => he i
    _ = (1/mass p m)*(∑ i : Fin m,entropyTerm (p i))+mass p m/Real.log 2 := by
      simp only [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_div,mass]
    _ ≤ 2*(∑' i,entropyTerm (p i))+1/Real.log 2 := by
      exact add_le_add
        ((mul_le_mul_of_nonneg_right hc2 hsumH0).trans
          (mul_le_mul_of_nonneg_left hsumH (by norm_num)))
        (div_le_div_of_nonneg_right (mass_le_one p hp hs ht m) hlog.le)

/-- A primitive-recursive dimension schedule yielding inverse-square Schmidt tails. -/
def stageDimension (B r : ℕ) : ℕ := 2^((B+1)*(r+1)*(r+1)+2)

theorem stageDimension_primrec : Primrec (fun p : ℕ × ℕ => stageDimension p.1 p.2) := by
  have he : Primrec (fun p : ℕ × ℕ => (p.1+1)*(p.2+1)*(p.2+1)+2) := by
    fun_prop
  exact (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) he

/-- Entropy gives the stated computable inverse-square tail rate. -/
theorem scheduled_tail (p : ℕ → ℝ) (hp : ∀ i,0 ≤ p i) (hs : Summable p)
    (ht : (∑' i,p i)=1) (ha : Antitone p)
    (hH : Summable (fun i => entropyTerm (p i))) (B r : ℕ)
    (hB : (∑' i,entropyTerm (p i)) ≤ B) :
    (∑' i,p (i+stageDimension B r+1)) ≤ 1/(r+1:ℝ)^2 := by
  let e := (B+1)*(r+1)*(r+1)+2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (e:ℝ)*Real.log 2 ≤ Real.log (stageDimension B r+2:ℝ) := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    change (2:ℝ)^e ≤ (2^e:ℕ)+2
    push_cast
    linarith
  have hden : (e:ℝ) ≤ Real.log (stageDimension B r+2:ℝ)/Real.log 2 :=
    (le_div_iff₀ hlog2).mpr hlog
  have hdenpos : 0 < Real.log (stageDimension B r+2:ℝ)/Real.log 2 := by
    apply div_pos _ hlog2
    apply Real.log_pos
    have hn : (0:ℝ) ≤ stageDimension B r := Nat.cast_nonneg _
    linarith
  have hrpos : 0 < (r+1:ℝ)^2 := by positivity
  apply (UpperEntropy.tail p hp hs ht ha hH B hB (stageDimension B r)).trans
  apply (div_le_div_iff₀ hdenpos hrpos).mpr
  have he : (e:ℝ)=(B+1:ℝ)*(r+1:ℝ)*(r+1:ℝ)+2 := by
    dsimp [e]
    push_cast
    rfl
  rw [he] at hden
  have hr : 0 ≤ (r:ℝ) := Nat.cast_nonneg r
  nlinarith

end Sigma2.UpperEntropyTruncation
