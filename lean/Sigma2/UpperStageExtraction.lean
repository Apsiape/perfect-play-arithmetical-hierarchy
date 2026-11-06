import Sigma2.UpperStageLimits
import Sigma2.UpperTransposeLimits

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
open Filter
namespace Sigma2.UpperStageExtraction
open UpperFiniteOperators

/-- All finite witnesses yield a stratum. The amplitude subsequence is refined by
one common WOT subsequence; both parties retain genuine normalized positive POVMs. -/
theorem stratum_of_finite_data (G : Game) (κ : ℕ) (hκ : 0<κ)
    (d : (n : ℕ) → Fin (n+1) → ℝ)
    (E : (n : ℕ) → QA G.scenario → AA G.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (F : (n : ℕ) → QB G.scenario → BB G.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (h0 : ∀ n,d n 0=1) (hd : ∀ n i,0≤d n i) (ha : ∀ n,Antitone (d n))
    (hb : ∀ n,(∑ i,d n i^2)≤κ)
    (hEpos : ∀ n x a,(E n x a).PosSemidef) (hFpos : ∀ n y b,(F n y b).PosSemidef)
    (hEsum : ∀ n x,∑ a,E n x a=1) (hFsum : ∀ n y,∑ b,F n y b=1)
    (hstage : ∀ n x y a b,0<G.distribution x y → G.accepts x y a b=false → ∀ i j,
      ‖(E n x a * Matrix.diagonal (fun i => (d n i : ℂ)) * (F n y b).transpose) i j‖^2
        ≤ (κ:ℝ)/(n+2)) : Stratum G κ := by
  obtain ⟨D,e,φ,hφ,hdiag,he0,hepos,heanti,hesum,hebudget,hD⟩ :=
    UpperFiniteAmplitudes.exists_norm_subsequence (κ:ℝ) d h0 hd ha hb
  let T (n : ℕ) : (QA G.scenario × AA G.scenario) ⊕ (QB G.scenario × BB G.scenario) → Op
    | .inl (x,a) => effect (φ n+1) 0 a (E (φ n) x a)
    | .inr (y,b) => effect (φ n+1) 0 b (F (φ n) y b)
  have hT n z : ‖T n z‖≤1 := by
    cases z with
    | inl z => exact effect_norm_le_one _ 0 z.2 _ (hEpos (φ n) z.1) (hEsum (φ n) z.1)
    | inr z => exact effect_norm_le_one _ 0 z.2 _ (hFpos (φ n) z.1) (hFsum (φ n) z.1)
  obtain ⟨L,ψ,hψ,_,hL⟩ := UpperWOTCompact.exists_common_subsequence T hT
  let A (x : QA G.scenario) (a : AA G.scenario) : Op := L (.inl (x,a))
  let B (y : QB G.scenario) (b : BB G.scenario) : Op := L (.inr (y,b))
  have hApos x a : Positive (A x a) :=
    UpperWeakLimits.positive _ _ (hL (.inl (x,a)))
      (fun n => effect_positive _ 0 a _ (hEpos (φ (ψ n)) x a))
  have hBpos y b : Positive (B y b) :=
    UpperWeakLimits.positive _ _ (hL (.inr (y,b)))
      (fun n => effect_positive _ 0 b _ (hFpos (φ (ψ n)) y b))
  have hAsum x : ∑ a,A x a=1 :=
    UpperWeakLimits.sum_eq_one _ _ (fun a => hL (.inl (x,a)))
      (fun n => effect_sum _ 0 _ (hEsum (φ (ψ n)) x))
  have hBsum y : ∑ b,B y b=1 :=
    UpperWeakLimits.sum_eq_one _ _ (fun b => hL (.inr (y,b)))
      (fun n => effect_sum _ 0 _ (hFsum (φ (ψ n)) y))
  let M : Measurements G.scenario := TensorLifts.measurements G.scenario A B hApos hBpos hAsum hBsum
  apply UpperStageLimits.stratum_of_convergent_stages G κ hκ d E F hEpos hFpos hEsum hFsum hstage
    (φ ∘ ψ) (hφ.comp hψ) D e hdiag he0 hepos heanti hesum hebudget
    (hD.comp hψ.tendsto_atTop) M (fun y b => UpperTranspose.transpose (B y b))
  · intro y b i j
    exact UpperTranspose.transpose_entry _ i j
  · intro x a
    exact hL (.inl (x,a))
  · intro y b
    have ht := UpperTransposeLimits.converges _ _ (hL (.inr (y,b)))
    simpa only [T,B,UpperTransposeLimits.transpose_effect,UpperStageLimits.bobTranspose,Function.comp_def] using ht

end Sigma2.UpperStageExtraction

