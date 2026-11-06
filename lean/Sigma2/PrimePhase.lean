import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace Sigma2.PrimePhase

/-- The elementary chord estimate used in the prime-phase counting proof. -/
theorem chord_lower (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    4 * min x (1-x) ≤ ‖Complex.exp (Complex.I * (2*Real.pi*x : ℝ)) - 1‖ := by
  have half_bound (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1/2) :
      2*y ≤ Real.sin (Real.pi*y) := by
    have h := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hy)
      (by nlinarith [Real.pi_pos] : Real.pi*y ≤ Real.pi/2)
    have he : 2/Real.pi*(Real.pi*y)=2*y := by field_simp
    rwa [he] at h
  have hs : 2*min x (1-x) ≤ Real.sin (Real.pi*x) := by
    by_cases hh : x ≤ 1/2
    · rw [min_eq_left (by linarith)]
      exact half_bound x hx hh
    · rw [min_eq_right (by linarith)]
      have h := half_bound (1-x) (by linarith) (by linarith)
      have he : Real.sin (Real.pi*(1-x))=Real.sin (Real.pi*x) := by
        rw [show Real.pi*(1-x)=Real.pi-Real.pi*x by ring, Real.sin_pi_sub]
      rwa [he] at h
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  have he : (2*Real.pi*x)/2=Real.pi*x := by ring
  rw [he, Real.norm_eq_abs]
  calc
    _ = 2*(2*min x (1-x)) := by ring
    _ ≤ 2*Real.sin (Real.pi*x) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ _ := le_abs_self _

/-- Distinct positive integers below a positive real bound number fewer than it. -/
theorem card_lt_value_bound {α : Type} [DecidableEq α] (s : Finset α)
    (f : α → ℕ) (hf : Set.InjOn f s) (a : ℝ) (ha : 0<a)
    (hb : ∀ x ∈ s, 0<f x ∧ (f x : ℝ)<a) : (s.card : ℝ)<a := by
  classical
  by_cases hs : s.Nonempty
  · let t := s.image f
    have ht : t.Nonempty := hs.image f
    let m := t.max' ht
    have hm : m ∈ t := Finset.max'_mem t ht
    have hsub : t ⊆ Finset.Icc 1 m := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨x,hx,rfl⟩
      exact Finset.mem_Icc.mpr ⟨(hb x hx).1, Finset.le_max' t (f x) hk⟩
    have hc : t.card ≤ m := by simpa using Finset.card_le_card hsub
    have hc' : s.card ≤ m := by simpa only [t, Finset.card_image_of_injOn hf] using hc
    rcases Finset.mem_image.mp hm with ⟨x,hx,he⟩
    have hm' : (m : ℝ)<a := by rw [← he]; exact (hb x hx).2
    exact (by exact_mod_cast hc' : (s.card : ℝ) ≤ m).trans_lt hm'
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simpa [he] using ha

/-- Finite prime-residue exclusion, independently of any Fock/clock model. -/
theorem good_residue (q : ℕ) (hq : Nat.Prime q) :
    ∃ k : ℕ, 0<k ∧ k<q ∧ ∀ t : ℕ, 0<t → t<q →
      (q:ℝ)*(1/2:ℝ)^(t+3) ≤
        min (((t*k)%q : ℕ):ℝ) ((q-(t*k)%q : ℕ):ℝ) := by
  classical
  let s : Finset ℕ := Finset.Icc 1 (q-1)
  let a : ℕ → ℝ := fun t => (q:ℝ)*(1/2:ℝ)^(t+3)
  let f : ℕ → ℕ → ℕ := fun t k => (t*k)%q
  let low : ℕ → Finset ℕ := fun t => s.filter (fun k => (f t k : ℝ)<a t)
  let high : ℕ → Finset ℕ := fun t => s.filter (fun k => ((q-f t k : ℕ):ℝ)<a t)
  let bad : ℕ → Finset ℕ := fun t => s.filter (fun k =>
    min (f t k : ℝ) ((q-f t k : ℕ):ℝ)<a t)
  have hmem {k : ℕ} : k ∈ s ↔ 0<k ∧ k<q := by
    simp only [s, Finset.mem_Icc]
    omega
  have hqR : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hap (t : ℕ) : 0<a t := by dsimp [a]; positivity
  have hf_range {t k : ℕ} (ht : t∈s) (hk : k∈s) : 0<f t k ∧ f t k<q := by
    have ht' := hmem.mp ht
    have hk' := hmem.mp hk
    refine ⟨?_, Nat.mod_lt _ hq.pos⟩
    apply Nat.pos_of_ne_zero
    intro he
    have hd : q ∣ t*k := Nat.dvd_of_mod_eq_zero he
    rcases hq.dvd_mul.mp hd with hd | hd
    · exact (Nat.not_dvd_of_pos_of_lt ht'.1 ht'.2) hd
    · exact (Nat.not_dvd_of_pos_of_lt hk'.1 hk'.2) hd
  have hf_inj {t : ℕ} (ht : t∈s) : Set.InjOn (f t) s := by
    intro k hk l hl he
    have ht' := hmem.mp ht
    have hc : q.Coprime t := hq.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt ht'.1 ht'.2)
    have he' : Nat.ModEq q (t*k) (t*l) := he
    have he'' := Nat.ModEq.cancel_left_of_coprime hc he'
    exact he''.eq_of_lt_of_lt (hmem.mp hk).2 (hmem.mp hl).2
  have hbad (t : ℕ) (ht : t∈s) : (bad t).card ≤ (low t).card+(high t).card := by
    apply (Finset.card_le_card (show bad t ⊆ low t ∪ high t from ?_)).trans
      (Finset.card_union_le _ _)
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hk,hb⟩
    rcases min_lt_iff.mp hb with hb | hb
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hk,hb⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hk,hb⟩))
  have hlow (t : ℕ) (ht : t∈s) : ((low t).card : ℝ)<a t := by
    apply card_lt_value_bound (low t) (f t)
      (fun k hk l hl he => hf_inj ht (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hl).1 he)
      (a t) (hap t)
    intro k hk
    exact ⟨(hf_range ht (Finset.mem_filter.mp hk).1).1, (Finset.mem_filter.mp hk).2⟩
  have hhigh (t : ℕ) (ht : t∈s) : ((high t).card : ℝ)<a t := by
    apply card_lt_value_bound (high t) (fun k => q-f t k) ?_ (a t) (hap t) ?_
    · intro k hk l hl he
      have hk' := hf_range ht (Finset.mem_filter.mp hk).1
      have hl' := hf_range ht (Finset.mem_filter.mp hl).1
      apply hf_inj ht (Finset.mem_filter.mp hk).1 (Finset.mem_filter.mp hl).1
      change q-f t k=q-f t l at he
      omega
    · intro k hk
      have hk' := hf_range ht (Finset.mem_filter.mp hk).1
      exact ⟨by omega, (Finset.mem_filter.mp hk).2⟩
  have hbadR (t : ℕ) (ht : t∈s) : ((bad t).card : ℝ) ≤ (q:ℝ)*(1/2:ℝ)^(t+2) := by
    have hb : ((bad t).card : ℝ) ≤ (low t).card+(high t).card := by exact_mod_cast hbad t ht
    have h1 := hlow t ht
    have h2 := hhigh t ht
    have he : 2*a t=(q:ℝ)*(1/2:ℝ)^(t+2) := by
      dsimp [a]
      rw [show t+3=(t+2)+1 by omega, pow_succ]
      ring
    linarith
  have hgeo : (∑ t ∈ s, (1/2:ℝ)^t) ≤ 1 := by
    have hs0 : 0∉s := by simp [s]
    have hsum := (summable_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)).sum_le_tsum
      (insert 0 s) (fun t _ => by positivity)
    rw [Finset.sum_insert hs0, pow_zero,
      tsum_geometric_of_abs_lt_one (by norm_num : |(1/2:ℝ)|<1)] at hsum
    norm_num at hsum
    linarith
  have hu : ((s.biUnion bad).card : ℝ) ≤ (q:ℝ)/4 := by
    calc
      _ ≤ ∑ t ∈ s, ((bad t).card : ℝ) := by exact_mod_cast (show (s.biUnion bad).card ≤ ∑ t ∈ s, (bad t).card from Finset.card_biUnion_le)
      _ ≤ ∑ t ∈ s, (q:ℝ)*(1/2:ℝ)^(t+2) := Finset.sum_le_sum hbadR
      _ = ((q:ℝ)/4)*(∑ t ∈ s, (1/2:ℝ)^t) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        rw [pow_add]
        norm_num
        ring
      _ ≤ _ := by nlinarith
  have hcard : (s.card : ℝ)=(q:ℝ)-1 := by
    have hc : s.card=q-1 := by simp [s]
    rw [hc, Nat.cast_sub (le_trans (by decide : 1≤2) hq.two_le)]
    norm_num
  have hq2 : (2:ℝ)≤q := by exact_mod_cast hq.two_le
  have hlt : (s.biUnion bad).card < s.card := by
    have hr : ((s.biUnion bad).card : ℝ) < (s.card : ℝ) := by
      rw [hcard]
      linarith
    exact_mod_cast hr
  have hex : ∃ k ∈ s, k ∉ s.biUnion bad := by
    by_contra he
    push_neg at he
    exact (not_le_of_gt hlt) (Finset.card_le_card he)
  obtain ⟨k,hk,hkbad⟩ := hex
  refine ⟨k,(hmem.mp hk).1,(hmem.mp hk).2,?_⟩
  intro t ht htq
  have ht' : t∈s := hmem.mpr ⟨ht,htq⟩
  have hn : k∉bad t := fun hb => hkbad (Finset.mem_biUnion.mpr ⟨t,ht',hb⟩)
  have hn' : ¬ min (f t k : ℝ) ((q-f t k : ℕ):ℝ)<a t := by
    intro hb
    exact hn (Finset.mem_filter.mpr ⟨hk,hb⟩)
  exact le_of_not_gt hn'

/-- Reduction of a power modulo an available root order. -/
theorem power_mod (z : ℂ) (q : ℕ) (hz : z^q=1) (t : ℕ) : z^t=z^(t%q) := by
  calc
    _ = z^(t%q+q*(t/q)) := congrArg (fun n => z^n) (Nat.mod_add_div t q).symm
    _ = _ := by rw [pow_add, pow_mul, hz, one_pow, mul_one]

/-- The standalone good-root theorem in ordinary complex-number language. -/
theorem good_root (q : ℕ) (hq : Nat.Prime q) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ q ∧ ∀ t : ℕ, 0<t → ¬q∣t →
      (1/2:ℝ)^(t+1) ≤ ‖ζ^t-1‖ := by
  obtain ⟨k,hk,hkq,hgood⟩ := good_residue q hq
  let ω : ℂ := Complex.exp (2*Real.pi*Complex.I/(q:ℂ))
  have hw : IsPrimitiveRoot ω q := Complex.isPrimitiveRoot_exp q hq.ne_zero
  have hc : k.Coprime q := (hq.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hk hkq)).symm
  let ζ := ω^k
  have hz : IsPrimitiveRoot ζ q := hw.pow_of_coprime k hc
  refine ⟨ζ,hz,?_⟩
  intro t ht hnt
  let r := t%q
  have hr : 0<r := Nat.pos_of_ne_zero (fun he => hnt (Nat.dvd_of_mod_eq_zero he))
  have hrq : r<q := Nat.mod_lt t hq.pos
  let m := (r*k)%q
  have hmq : m<q := Nat.mod_lt _ hq.pos
  have hqR : (0:ℝ)<q := by exact_mod_cast hq.pos
  have hmR : (0:ℝ)≤m := by positivity
  have hmqR : (m:ℝ)≤q := by exact_mod_cast hmq.le
  have ha := hgood r hr hrq
  have hmlow : (q:ℝ)*(1/2:ℝ)^(r+3) ≤ m := ha.trans (min_le_left _ _)
  have hmhigh : (q:ℝ)*(1/2:ℝ)^(r+3) ≤ (q:ℝ)-(m:ℝ) := by
    have h := ha.trans (min_le_right _ _)
    rwa [Nat.cast_sub hmq.le] at h
  have hdivision : ((m:ℝ)/(q:ℝ))*(q:ℝ)=m := div_mul_cancel₀ _ hqR.ne'
  have hmin : (1/2:ℝ)^(r+3) ≤ min ((m:ℝ)/(q:ℝ)) (1-(m:ℝ)/(q:ℝ)) := by
    apply le_min
    · apply (le_div_iff₀ hqR).mpr
      nlinarith
    · nlinarith
  have hchord := chord_lower ((m:ℝ)/(q:ℝ)) (by positivity)
    ((div_le_one hqR).mpr hmqR)
  have hexp : ω^m=Complex.exp (Complex.I*(2*Real.pi*((m:ℝ)/(q:ℝ)) : ℝ)) := by
    dsimp [ω]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hepow : ζ^r=ω^m := by
    dsimp [ζ,m]
    rw [← pow_mul, Nat.mul_comm k r]
    exact power_mod ω q hw.pow_eq_one (r*k)
  have hsmall : (1/2:ℝ)^(r+1) ≤ ‖ζ^r-1‖ := by
    rw [hepow,hexp]
    calc
      _ = 4*(1/2:ℝ)^(r+3) := by
        rw [show r+3=(r+1)+2 by omega, pow_add]
        norm_num
        ring
      _ ≤ 4*min ((m:ℝ)/(q:ℝ)) (1-(m:ℝ)/(q:ℝ)) :=
        mul_le_mul_of_nonneg_left hmin (by norm_num)
      _ ≤ _ := hchord
  have hpow : (1/2:ℝ)^(t+1) ≤ (1/2:ℝ)^(r+1) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right (Nat.mod_le t q) 1)
  rw [power_mod ζ q hz.pow_eq_one t]
  exact hpow.trans hsmall

#print axioms good_root
end Sigma2.PrimePhase
