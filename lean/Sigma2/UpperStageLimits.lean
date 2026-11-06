import Sigma2.UpperCompression
import Sigma2.UpperWeakLimits
import Sigma2.UpperDiagonalVectors

noncomputable section
open scoped BigOperators ComplexOrder Matrix
open Filter
namespace Sigma2.UpperStageLimits
open UpperFiniteOperators

def alice (G : Game) (E : (n : ℕ) → QA G.scenario → AA G.scenario →
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (n : ℕ) (x : QA G.scenario) (a : AA G.scenario) : Op :=
  effect (n+1) 0 a (E n x a)

def bobTranspose (G : Game) (F : (n : ℕ) → QB G.scenario → BB G.scenario →
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ) (n : ℕ) (y : QB G.scenario) (b : BB G.scenario) : Op :=
  effect (n+1) 0 b (F n y b).transpose

/-- The limiting-operator part of the stage converse. The remaining extraction
step must supply common weak limits of the effects appearing here. -/
theorem stratum_of_convergent_stages (G : Game) (κ : ℕ) (hκ : 0<κ)
    (d : (n : ℕ) → Fin (n+1) → ℝ)
    (E : (n : ℕ) → QA G.scenario → AA G.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (F : (n : ℕ) → QB G.scenario → BB G.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (hEpos : ∀ n x a,(E n x a).PosSemidef) (hFpos : ∀ n y b,(F n y b).PosSemidef)
    (hEsum : ∀ n x,∑ a,E n x a=1) (hFsum : ∀ n y,∑ b,F n y b=1)
    (hstage : ∀ n x y a b,0<G.distribution x y → G.accepts x y a b=false → ∀ i j,
      ‖(E n x a * Matrix.diagonal (fun i => (d n i : ℂ)) * (F n y b).transpose) i j‖^2
        ≤ (κ:ℝ)/(n+2))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (D : Op) (e : ℕ → ℝ) (hdiag : UpperAmplitudes.Diagonal D e)
    (he0 : e 0=1) (hepos : ∀ i,0≤e i) (heanti : Antitone e)
    (hesum : Summable (fun i => e i^2)) (hebudget : (∑' i,e i^2)≤κ)
    (hD : Tendsto (fun n => extend (φ n+1) (Matrix.diagonal (fun i => (d (φ n) i : ℂ))))
      atTop (nhds D))
    (M : Measurements G.scenario) (Ftr : QB G.scenario → BB G.scenario → Op)
    (ht : ∀ y b i j,entry (Ftr y b) i j=entry (M.bob y b) j i)
    (hE : ∀ x a,UpperWeakLimits.Converges (fun n => alice G E (φ n) x a) (M.alice x a))
    (hF : ∀ y b,UpperWeakLimits.Converges (fun n => bobTranspose G F (φ n) y b) (Ftr y b)) :
    Stratum G κ := by
  apply UpperDiagonalVectors.stratum_of_sandwiches G κ hκ M D e hesum he0 hdiag hebudget Ftr ht
  intro x y a b hw ha
  have bE : ∃ C : ℝ,∀ n,‖alice G E (φ n) x a‖≤C := by
    refine ⟨1,fun n => effect_norm_le_one (φ n+1) 0 a (E (φ n) x) (hEpos (φ n) x) (hEsum (φ n) x)⟩
  have bF : ∃ C : ℝ,∀ n,‖bobTranspose G F (φ n) y b‖≤C := by
    refine ⟨1,fun n => effect_norm_le_one (φ n+1) 0 b
      (fun b => (F (φ n) y b).transpose) (fun b => (hFpos (φ n) y b).transpose) ?_⟩
    have hh := congrArg Matrix.transpose (hFsum (φ n) y)
    simpa only [Matrix.transpose_sum,Matrix.transpose_one] using hh
  have hconv := UpperCompact.sandwiches
    (fun n => extend (φ n+1) (Matrix.diagonal (fun i => (d (φ n) i : ℂ))))
    (fun n => alice G E (φ n) x a) (fun n => bobTranspose G F (φ n) y b)
    D (M.alice x a) (Ftr y b) hD
    (UpperFiniteAmplitudes.diagonal_compact D e hdiag hepos heanti hesum)
    (hE x a) (hF y b) bE bF
  apply UpperWeakLimits.zero_of_stage_bounds _ _ hconv (κ:ℝ) φ hφ
  intro n i j
  change ‖entry (effect (φ n+1) 0 a (E (φ n) x a) *
    extend (φ n+1) (Matrix.diagonal (fun i => (d (φ n) i : ℂ))) *
    effect (φ n+1) 0 b (F (φ n) y b).transpose) i j‖^2 ≤ _
  rw [effect_sandwich,extend_entry]
  split_ifs with hi hj
  · exact hstage (φ n) x y a b hw ha ⟨i,hi⟩ ⟨j,hj⟩
  · simp only [norm_zero,zero_pow (by decide : 2≠0)]
    positivity
  · simp only [norm_zero,zero_pow (by decide : 2≠0)]
    positivity

end Sigma2.UpperStageLimits
