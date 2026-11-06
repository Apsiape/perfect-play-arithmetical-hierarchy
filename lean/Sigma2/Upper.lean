import Sigma2.EntropyPolynomialProof
import Sigma2.Preliminaries
import Sigma2.UpperAnalytic
import Sigma2.UpperCompact
import Sigma2.UpperAmplitudes
import Sigma2.UpperEntropy
import Sigma2.UpperRealArithmetic
import Sigma2.UpperGameDecision
import Sigma2.UpperCompression
import Sigma2.UpperStageLimits
import Sigma2.UpperStageExtraction
import Sigma2.UpperSchmidtOperators
import Sigma2.UpperSchmidtState
import Sigma2.UpperEntropySlack
import Sigma2.UpperEntropyCanonical
import Sigma2.UpperEntropyFeasible
import Sigma2.UpperEntropyDecision
import Sigma2.UpperEntropyAssembly
import Sigma2.UpperEntropyQuantifiers

noncomputable section
open scoped BigOperators ComplexOrder
namespace Sigma2.Upper

def WOT (T : ℕ → Op) (L : Op) : Prop :=
  ∀ u v : H, Filter.Tendsto (fun n => inner ℂ u (T n v)) Filter.atTop (nhds (inner ℂ u (L v)))

def Compact (T : Op) : Prop := IsCompact (closure (T '' Metric.closedBall 0 1))

structure Amplitude (κ : ℕ) where
  op : Op
  d : ℕ → ℝ
  diagonal : ∀ i j, entry op i j = if i=j then (d i : ℂ) else 0
  first : d 0=1
  nonneg : ∀ i, 0 ≤ d i
  decreasing : Antitone d
  summable : Summable (fun i => d i ^ 2)
  budget : (∑' i, d i ^ 2) ≤ κ

/-- Eq. (1), normalization by the largest Schmidt coefficient. -/
theorem schmidt_normalization {s} (S : PureStrategy s) :
    ∃ κ : ℕ, 0 < κ ∧ 1/(κ:ℝ) ≤ largestSchmidt S.vector := by
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt (UpperAnalytic.largest_pos S.vector S.unit)
  exact ⟨k+1,Nat.succ_pos _,le_of_lt (by simpa only [Nat.cast_add,Nat.cast_one] using hk)⟩

/-- Sorted normalized Schmidt amplitudes from the exact PureStrategy interface.
The remaining forward obligation transports the two POVMs to these coordinates. -/
theorem schmidt_amplitude {s} (S : PureStrategy s) (κ : ℕ) (hκ : 0<κ)
    (hb : 1/(κ:ℝ)≤largestSchmidt S.vector) :
    ∃ (D : Amplitude κ) (q : ℕ → ℝ) (u : ℕ → H),
      Orthonormal ℂ u ∧ (∀ i,0≤q i) ∧ Summable q ∧ (∑' i,q i)=1 ∧ Antitone q ∧
      (∀ i,D.d i^2=q i/q 0) ∧ q 0=largestSchmidt S.vector ∧
      (∀ v,(UpperSchmidtSpectrum.density S.vector S.unit).op v=
        ∑' i,((q i:ℂ)*inner ℂ (u i) v) • u i) := by
  obtain ⟨d,q,u,h0,hd,ha,hs,hbudget,hu,hq,hqs,hqt,hqa,hd2,htop,he⟩ :=
    UpperSchmidtSpectrum.normalized_spectrum S.vector S.unit κ hκ hb
  have hbound i : |d i|≤1 := by
    rw [abs_of_nonneg (hd i)]
    exact (ha (Nat.zero_le i)).trans_eq h0
  exact ⟨⟨UpperSchmidtOperators.diagonalOp d hbound,d,
    UpperSchmidtOperators.diagonalOp_diagonal d hbound,h0,hd,ha,hs,hbudget⟩,
    q,u,hu,hq,hqs,hqt,hqa,hd2,htop,he⟩
/-- Zero-event vectorization: Ftr is the genuine matrix transpose, not an adjoint. -/
theorem zero_sandwich {s} (M : Measurements s) (x : QA s) (y : QB s)
    (a : AA s) (b : BB s) (D Ftr : Op)
    (ht : ∀ i j, entry Ftr i j=entry (M.bob y b) j i)
    (v : AB) (hv : ∀ i j, v (i,j)=entry D i j) :
    (inner ℂ v ((M.left x a*M.right y b) v)).re=0 ↔ M.alice x a*D*Ftr=0 := by
  exact UpperAnalytic.zero_sandwich M x y a b D Ftr ht v hv

/-- Eq. (2), common tail bound; coordinates are zero based. -/
theorem amplitude_tail {κ} (D : Amplitude κ) (n : ℕ) :
    D.d n ≤ Real.sqrt ((κ:ℝ)/(n+1)) := by
  exact UpperAnalytic.square_tail D.d D.decreasing D.nonneg D.summable κ D.budget n

theorem amplitude_compact_family (κ : ℕ) :
    IsCompact {T : Op | ∃ D : Amplitude κ, D.op=T} := by
  have heq : {T : Op | ∃ D : Amplitude κ, D.op=T}=UpperAmplitudes.Family κ := by
    ext T
    constructor
    · rintro ⟨D,rfl⟩
      exact ⟨D.d,D.diagonal,D.first,D.nonneg,D.decreasing,D.summable,D.budget⟩
    · rintro ⟨d,hdiag,hfirst,hnonneg,hanti,hsumm,hbudget⟩
      exact ⟨⟨T,d,hdiag,hfirst,hnonneg,hanti,hsumm,hbudget⟩,rfl⟩
  rw [heq]
  exact UpperAmplitudes.compact_family κ

/-- Lemma 3.2, Compact sandwiches. -/
theorem lemma_3_1_compact_sandwiches (D E F : ℕ → Op) (D₀ E₀ F₀ : Op)
    (hD : Filter.Tendsto D Filter.atTop (nhds D₀)) (hc : Compact D₀)
    (hE : WOT E E₀) (hF : WOT F F₀)
    (bE : ∃ C : ℝ, ∀ n, ‖E n‖ ≤ C) (bF : ∃ C : ℝ, ∀ n, ‖F n‖ ≤ C) :
    WOT (fun n => E n*D n*F n) (E₀*D₀*F₀) := by
  exact UpperCompact.sandwiches D E F D₀ E₀ F₀ hD
    ((isCompactOperator_iff_isCompact_closure_image_closedBall D₀.toLinearMap zero_lt_one).mpr hc)
    hE hF bE bF

/-- Eq. (3): n+1 dimensional stage, including every losing positive-weight tuple. -/
def FiniteStage (G : Game) (κ n : ℕ) : Prop :=
  ∃ (d : Fin (n+1) → ℝ)
    (E : QA G.scenario → AA G.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (F : QB G.scenario → BB G.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ),
    d 0=1 ∧ (∀ i, 0 ≤ d i) ∧ Antitone d ∧ (∑ i, d i^2) ≤ κ ∧
    (∀ x a, (E x a).PosSemidef) ∧ (∀ y b, (F y b).PosSemidef) ∧
    (∀ x, ∑ a, E x a=1) ∧ (∀ y, ∑ b, F y b=1) ∧
    (∀ x y a b, 0 < G.distribution x y → G.accepts x y a b=false →
      ∀ i j, ‖(E x a * Matrix.diagonal (fun k => (d k : ℂ)) * (F y b).transpose) i j‖^2 ≤
        (κ:ℝ)/(n+2))

/-- Every normalized diagonal perfect witness supplies the frozen finite stages.
The Schmidt-coordinate transport needed to obtain this witness from a general
stratum strategy is a separate obligation. -/
theorem finite_stage_of_sandwiches (G : Game) (κ n : ℕ) (D : Amplitude κ)
    (M : Measurements G.scenario) (Ftr : QB G.scenario → BB G.scenario → Op)
    (ht : ∀ y b i j,entry (Ftr y b) i j=entry (M.bob y b) j i)
    (hz : ∀ x y a b,0<G.distribution x y → G.accepts x y a b=false →
      M.alice x a*D.op*Ftr y b=0) : FiniteStage G κ n := by
  let E := fun x a => UpperFiniteOperators.compress (n+1) (M.alice x a)
  let F := fun y b => UpperFiniteOperators.compress (n+1) (M.bob y b)
  have hnorm {ι : Type} [Fintype ι] [DecidableEq ι] (A : ι → Op)
      (hp : ∀ i,Positive (A i)) (hs : ∑ i,A i=1) (i : ι) : ‖A i‖≤1 := by
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
      (ContinuousLinearMap.nonneg_iff_isPositive.mpr (hp i))).mpr
    apply sub_nonneg.mp
    apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
    rw [← hs]
    exact Preliminaries.positive_sum_erase A hp i
  have hFt y b : Ftr y b=UpperTranspose.transpose (M.bob y b) := by
    apply UpperAnalytic.entry_ext
    intro i j
    rw [ht,UpperTranspose.transpose_entry]
  refine ⟨(fun i => D.d i),E,F,D.first,(fun i => D.nonneg i),
    (fun i j hij => D.decreasing hij),?_,
    (fun x a => UpperFiniteOperators.compress_positive _ _ (M.alice_pos x a)),
    (fun y b => UpperFiniteOperators.compress_positive _ _ (M.bob_pos y b)),
    (fun x => UpperFiniteOperators.compress_sum _ _ (M.alice_sum x)),
    (fun y => UpperFiniteOperators.compress_sum _ _ (M.bob_sum y)),?_⟩
  · have hh := (D.summable.sum_le_tsum (Finset.range (n+1))
      (fun i _ => sq_nonneg (D.d i))).trans D.budget
    rw [← Fin.sum_univ_eq_sum_range (fun i => D.d i^2)] at hh
    exact hh
  · intro x y a b hw ha i j
    have hf : ‖Ftr y b‖≤1 := by
      rw [hFt,UpperTranspose.transpose_norm]
      exact hnorm _ (M.bob_pos y) (M.bob_sum y) b
    have hh := UpperCompression.compression_entry_square (κ:ℝ) n
      (M.alice x a) D.op (Ftr y b) D.d D.diagonal D.nonneg D.decreasing D.summable D.budget
      (hnorm _ (M.alice_pos x) (M.alice_sum x) a) hf (hz x y a b hw ha) i j
    have hc : UpperFiniteOperators.compress (n+1) (Ftr y b) = (F y b).transpose := by
      ext i j
      exact ht y b i j
    rw [hc] at hh
    exact hh

/-- The polynomial witness interpretation agrees with the frozen finite stage. -/
theorem finite_stage_witness (r : RawGame) (hr : ValidRawGame r) (κ n : ℕ) :
    FiniteStage (gameOfRaw r hr) κ n ↔ UpperStageSyntax.Witness r.1 κ n (UpperGameCompiler.rawLosing r) := by
  have hl (x : QA r.1) (y : QB r.1) (a : AA r.1) (b : BB r.1) :
      UpperGameCompiler.rawLosing r x y a b = true ↔
        0 < rawDistribution r x y ∧ rawAccepts r x y a b = false := by
    change (decide (0 < UpperGameCompiler.rawWeight r x y) && !UpperGameCompiler.rawWin r x y a b) = true ↔ _
    rw [Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true_eq_eq_false]
    rfl
  simp only [FiniteStage,UpperStageSyntax.Witness,gameOfRaw,hl,and_imp]
  all_goals rfl
/-- The effective sentence compiler handles valid decoded tables and rejects invalid codes. -/
theorem finite_stage_sentence_truth (c κ n : ℕ) :
    UpperRealArithmetic.OrderedRingTruth (UpperGameCompiler.codeSentence c κ n) ↔
      GameProperty (fun G => FiniteStage G κ n) c := by
  rw [UpperGameCompiler.codeSentence_truth]
  constructor
  · rintro ⟨r,hr,hv,hw⟩
    refine ⟨gameOfRaw r hv,?_,(finite_stage_witness r hv κ n).mpr hw⟩
    simp [decodeGame,hr,hv]
  · rintro ⟨G,hG,hstage⟩
    unfold decodeGame at hG
    cases hr : Encodable.decode (α := RawGame) c with
    | none => simp [hr] at hG
    | some r =>
        by_cases hv : ValidRawGame r
        · have hg : gameOfRaw r hv = G := by simpa [hr,hv] using hG
          subst G
          exact ⟨r,rfl,hv,(finite_stage_witness r hv κ n).mp hstage⟩
        · simp [hr,hv] at hG

/-- Uniform finite-stage decision using the effective polynomial translation and
an explicit decision procedure for the existential theory of the reals. -/
theorem finite_stage_computable_of_tarski (hT : UpperRealArithmetic.TarskiDecision) :
    ∃ R : (ℕ × ℕ) × ℕ → Bool, Computable R ∧ ∀ c k n,
      R ((c,k),n)=true ↔ GameProperty (fun G => FiniteStage G (k+1) n) c := by
  classical
  have hi : Computable (fun p : (ℕ × ℕ) × ℕ => (p.1.1,p.1.2+1,p.2)) :=
    ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.succ.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd)).to_comp
  have hs := UpperGameCompiler.codeSentence_computable.comp hi
  have hR := hT.decide.comp hs
  refine ⟨fun p => decide (UpperRealArithmetic.OrderedRingTruth
    (UpperGameCompiler.codeSentence p.1.1 (p.1.2+1) p.2)),hR,?_⟩
  intro c k n
  simp only [decide_eq_true_eq]
  exact finite_stage_sentence_truth c (k+1) n

/-- The exact Schmidt-coordinate strategy and normalized amplitudes yield all finite stages. -/
theorem finite_stages_of_stratum (G : Game) (κ : ℕ) (h : Stratum G κ) :
    ∀ n,FiniteStage G κ n := by
  obtain ⟨hκ,S,hS,hbound⟩ := h
  obtain ⟨D,q,u,hu,hq,hqs,hqt,hqa,hd2,htop,he⟩ := schmidt_amplitude S κ hκ hbound
  obtain ⟨T,hTv,hprob⟩ := UpperSchmidtState.exists_strategy S q u hq hqs hqt hu he
  let t : ℝ := Real.sqrt (q 0)
  have hq0 : 0<q 0 := htop ▸ UpperAnalytic.largest_pos S.vector S.unit
  have ht : 0<t := Real.sqrt_pos.mpr hq0
  have hcoef (i : ℕ) : Real.sqrt (q i)=t*D.d i := by
    have hh : (t*D.d i)^2=q i := by
      rw [mul_pow,show t^2=q 0 from Real.sq_sqrt hq0.le,hd2]
      field_simp
    nlinarith [Real.sq_sqrt (hq i),Real.sqrt_nonneg (q i),mul_nonneg ht.le (D.nonneg i)]
  let Ftr := fun y b => UpperTranspose.transpose (T.measurements.bob y b)
  have hFtr y b i j : entry (Ftr y b) i j=entry (T.measurements.bob y b) j i :=
    UpperTranspose.transpose_entry _ i j
  have hv (i j : ℕ) : T.vector (i,j)=entry ((t:ℂ) • D.op) i j := by
    change T.vector (i,j)=(t:ℂ)*entry D.op i j
    rw [hTv,UpperSchmidtState.vector_apply,D.diagonal]
    by_cases hij : i=j
    · simp only [hij,ite_true,← Complex.ofReal_mul,hcoef]
    · simp [hij]
  have hz x y a b (hw : 0<G.distribution x y) (ha : G.accepts x y a b=false) :
      T.measurements.alice x a*D.op*Ftr y b=0 := by
    have hp : S.probability x y a b=0 := by
      have hh := Preliminaries.losing_event_le_loss G (normalOfPure S) x y a b
      rw [ha,normalOfPure_probability,show loss G (normalOfPure S)=0 from hS] at hh
      have hw' : (0:ℝ)<G.distribution x y := by exact_mod_cast hw
      have hn := Preliminaries.pure_probability_nonnegative S x y a b
      simp only [Bool.false_eq_true,↓reduceIte] at hh
      nlinarith
    have hp' : (inner ℂ T.vector ((T.measurements.left x a*T.measurements.right y b) T.vector)).re=0 :=
      (hprob x y a b).trans hp
    have hh := (zero_sandwich T.measurements x y a b ((t:ℂ) • D.op) (Ftr y b)
      (hFtr y b) T.vector hv).mp hp'
    have hscalar : (t:ℂ) • (T.measurements.alice x a*D.op*Ftr y b)=0 := by
      simpa only [mul_smul_comm,smul_mul_assoc] using hh
    exact (smul_eq_zero.mp hscalar).resolve_left (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))
  exact fun n => finite_stage_of_sandwiches G κ n D T.measurements Ftr hFtr hz
/-- The compact converse with all extraction steps discharged. -/
theorem stratum_of_finite_stages (G : Game) (κ : ℕ) (hκ : 0<κ)
    (h : ∀ n,FiniteStage G κ n) : Stratum G κ := by
  choose d E F h0 hd ha hb hEpos hFpos hEsum hFsum hstage using h
  exact UpperStageExtraction.stratum_of_finite_data G κ hκ d E F
    h0 hd ha hb hEpos hFpos hEsum hFsum hstage

/-- Decoding is unique, so the witnesses for all stages refer to the same game. -/
theorem stages_decoding (c κ : ℕ) :
    GameProperty (fun G => ∀ n,FiniteStage G κ n) c ↔
      ∀ n,GameProperty (fun G => FiniteStage G κ n) c := by
  constructor
  · rintro ⟨G,hG,h⟩ n
    exact ⟨G,hG,h n⟩
  · intro h
    obtain ⟨G,hG,_⟩ := h 0
    refine ⟨G,hG,fun n => ?_⟩
    obtain ⟨G',hG',hs⟩ := h n
    have he : G'=G := Option.some.inj (hG'.symm.trans hG)
    exact he ▸ hs

/-- The decoded-code converse of Eq. (4), with no admitted dependency. -/
theorem codeStratum_of_stages (c k : ℕ)
    (h : ∀ n,GameProperty (fun G => FiniteStage G (k+1) n) c) : CodeStratum c (k+1) := by
  obtain ⟨G,hG,hs⟩ := (stages_decoding c (k+1)).mpr h
  exact ⟨G,hG,stratum_of_finite_stages G (k+1) (Nat.succ_pos _) hs⟩
/-- Eq. (4), both compression and the compact-sandwich converse. -/
theorem stratum_iff_stages (c k : ℕ) :
    CodeStratum c (k+1) ↔ ∀ n, GameProperty (fun G => FiniteStage G (k+1) n) c := by
  constructor
  · rintro ⟨G,hG,hs⟩ n
    exact ⟨G,hG,finite_stages_of_stratum G (k+1) hs n⟩
  · exact codeStratum_of_stages c k

theorem spatial_union (c : ℕ) :
    SpatialPerfect c ↔ ∃ κ, 0 < κ ∧ CodeStratum c κ := by
  constructor
  · rintro ⟨G,hG,hperfect⟩
    obtain ⟨S,hS⟩ := (Preliminaries.normal_pure_perfect_equivalence G).mp hperfect
    obtain ⟨κ,hκ,hbound⟩ := schmidt_normalization S
    exact ⟨κ,hκ,G,hG,hκ,S,hS,hbound⟩
  · rintro ⟨κ,_,G,hG,_,S,hS,_⟩
    exact ⟨G,hG,normalOfPure S,hS⟩

theorem spatial_union_successor (c : ℕ) :
    SpatialPerfect c ↔ ∃ k, CodeStratum c (k+1) := by
  rw [spatial_union]
  constructor
  · rintro ⟨κ,hκ,h⟩
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hκ)
    exact ⟨k,h⟩
  · rintro ⟨k,h⟩; exact ⟨k+1,Nat.succ_pos _,h⟩

/-- Conditional assembly using the proved finite-stage compiler and stage equivalence. -/
theorem uniform_strata_piOne_of_tarski (hT : UpperRealArithmetic.TarskiDecision) :
    PiOne (fun ek : ℕ × ℕ => CodeStratum ek.1 (ek.2+1)) := by
  obtain ⟨R,hR,h⟩ := finite_stage_computable_of_tarski hT
  refine ⟨R,hR,?_⟩
  rintro ⟨c,k⟩
  exact (stratum_iff_stages c k).trans (forall_congr' (fun n => (h c k n).symm))

/-- Conditional spatial membership from the effective compiler and proved stage equivalence. -/
theorem spatial_sigmaTwo_of_tarski (hT : UpperRealArithmetic.TarskiDecision) :
    SigmaTwo SpatialPerfect := by
  obtain ⟨R,hR,h⟩ := uniform_strata_piOne_of_tarski hT
  refine ⟨(fun e => R ((e.1,e.2.1),e.2.2)),?_,?_⟩
  · exact hR.comp ((Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd))
  · intro c
    exact (spatial_union_successor c).trans (exists_congr (fun k => h (c,k)))

/-- Eq. (5), entropy tightness in a sorted distribution. -/
theorem entropy_tail (p : ℕ → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : Summable p)
    (ht : (∑' i, p i)=1) (hd : Antitone p)
    (hH : Summable (fun i => entropyTerm (p i))) (B : ℝ)
    (hB : (∑' i, entropyTerm (p i)) ≤ B) (n : ℕ) :
    (∑' i, p (i+n+1)) ≤ B / (Real.log (n+2) / Real.log 2) := by
  exact UpperEntropy.tail p hp hs ht hd hH B hB n

/-- Section 3.4, effective rational polynomial approximations with explicit uniform error. -/
theorem entropy_polynomial_approximation :
    ∃ coeff : ℕ × ℕ → List (ℤ × ℕ), Computable coeff ∧ ∀ n k, 0 < k →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        |((coeff (n,k)).zipIdx.map (fun qc => ((qc.1.1:ℝ)/(qc.1.2+1))*t^qc.2)).sum-entropyTerm t| ≤
          1/((n+1)*(k:ℝ)) := by
  exact EntropyPolynomial.entropy_polynomial_approximation_proof

/-- Rational polynomial entropy approximations, at dimension n+1 and precision k+1. -/
def EntropyApproximants (H : ℕ → ℕ → Polynomial ℚ) : Prop :=
  ∀ n k (p : Fin (n+1) → ℝ), (∀ i, 0 ≤ p i) → (∑ i,p i)=1 →
    |(∑ i,(H n k).eval₂ (algebraMap ℚ ℝ) (p i))-
      (∑ i,entropyTerm (p i))| ≤ 1/(k+1:ℝ)

/-- The clock development coefficient theorem supplies exactly the frozen finite
approximants. The proof uses only the three standard axioms. -/
theorem entropy_approximants :
    ∃ coeff : ℕ × ℕ → List (ℤ × ℕ),Computable coeff ∧
      EntropyApproximants (fun n k => UpperEntropyPolynomial.polynomial (coeff (n,k+1))) := by
  obtain ⟨coeff,hc,he⟩ := entropy_polynomial_approximation
  exact ⟨coeff,hc,UpperEntropyPolynomial.finite_approximation coeff he⟩

def EntropyStage (G : Game) (B n : ℕ) (η : ℝ) : Prop :=
  ∃ S : PureStrategy G.scenario, FiniteSupport S (n+1) ∧
    loss G (normalOfPure S) ≤ η ∧
    ∃ h : Density, MarginalA (normalOfPure S) h ∧
      ∃ (p : ℕ → ℝ) (u : ℕ → H),
        (∀ i,0 ≤ p i) ∧ Summable p ∧ (∑' i,p i)=1 ∧ Antitone p ∧ Orthonormal ℂ u ∧
        (∀ i : ℕ, n + 1 ≤ i → p i = 0) ∧
        (∀ v,h.op v=∑' i,((p i:ℂ)*inner ℂ (u i) v) • u i) ∧
        (∑ i : Fin (n+1),entropyTerm (p i)) ≤ (B:ℝ)+1/(n+1:ℝ)

/-- The finite real-algebraic relaxation in the paper; amplitudes and POVMs are
finite matrices, the trace norm/entropy is never supplied to QE as an oracle. -/
def EntropyRelaxation (G : Game) (B n k : ℕ) (η : ℚ) (H : Polynomial ℚ) : Prop :=
  ∃ (p t : Fin (n+1) → ℝ)
    (E : QA G.scenario → AA G.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (F : QB G.scenario → BB G.scenario → Matrix (Fin (n+1)) (Fin (n+1)) ℂ),
    (∀ i,0≤p i) ∧ (∑ i,p i)=1 ∧ Antitone p ∧
    (∀ i,0≤t i ∧ t i^2=p i) ∧
    (∀ x a,(E x a).PosSemidef) ∧ (∀ y b,(F y b).PosSemidef) ∧
    (∀ x,∑ a,E x a=1) ∧ (∀ y,∑ b,F y b=1) ∧
    (∑ x,∑ y,∑ a,∑ b, if G.accepts x y a b then 0 else
      (G.distribution x y:ℝ)*(∑ i,∑ j,
        (t i:ℂ)*(t j:ℂ)*E x a i j*F y b i j).re) ≤ (η:ℝ) ∧
    (∑ i,H.eval₂ (algebraMap ℚ ℝ) (p i)) ≤ (B:ℝ)+1/(n+1:ℝ)+1/(k+1:ℝ)

/-- The entropy-relaxation compiler agrees with the original frozen predicate. -/
theorem entropy_relaxation_sentence_truth (c B n k : ℕ) (η : ℚ) (a : List (ℤ × ℕ)) :
    UpperRealArithmetic.OrderedRingTruth (UpperEntropyEffective.codeSentence c B n k η a) ↔
      GameProperty (fun G => EntropyRelaxation G B n k η (UpperEntropyPolynomial.polynomial a)) c := by
  rw [UpperEntropyDecision.codeSentence_truth_game]
  constructor
  · rintro ⟨G,hG,⟨p,t,E,F⟩,hf,he⟩
    obtain ⟨hp,hs,ha,ht,hE,hF,hEs,hFs,hl⟩ := hf
    exact ⟨G,hG,p,t,E,F,hp,hs,ha,ht,hE,hF,hEs,hFs,hl,he⟩
  · rintro ⟨G,hG,p,t,E,F,hp,hs,ha,ht,hE,hF,hEs,hFs,hl,he⟩
    exact ⟨G,hG,(p,t,E,F),⟨hp,hs,ha,ht,hE,hF,hEs,hFs,hl⟩,he⟩

/-- Uniform, genuinely computable finite entropy-relaxation decisions under Tarski. -/
theorem entropy_relaxation_computable_of_tarski (hT : UpperRealArithmetic.TarskiDecision) :
    ∃ R : UpperEntropyEffective.CodeInput → Bool,Computable R ∧ ∀ c B n k η a,
      R (c,B,n,k,η,a)=true ↔
        GameProperty (fun G => EntropyRelaxation G B n k η (UpperEntropyPolynomial.polynomial a)) c := by
  classical
  refine ⟨fun p => decide (UpperRealArithmetic.OrderedRingTruth
    (UpperEntropyEffective.codeSentence p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)),
    (UpperEntropyDecision.computable_truth hT).decide,?_⟩
  intro c B n k η a
  simp only [decide_eq_true_eq]
  exact entropy_relaxation_sentence_truth c B n k η a

/-- The frozen finite entropy stage is exactly finite Schmidt/POVM feasibility
with the true entropy bound. Both directions use the actual reduced density. -/
theorem entropy_stage_witness (G : Game) (B n : ℕ) (η : ℚ) :
    EntropyStage G B n η ↔
      ∃ z : UpperEntropyFinite.Data G.scenario (n+1),
        UpperEntropyFinite.Feasible G (n+1) η z ∧
        (∑ i,entropyTerm (z.1 i)) ≤ (B:ℝ)+1/(n+1:ℝ) := by
  constructor
  · rintro ⟨S,hfinite,hl,h,hm,p,u,hp,hs,ht,ha,hu,hz,he,hent⟩
    obtain ⟨z,hf,hp'⟩ := UpperEntropyFinite.data_of_spectrum G (n+1) η
      S hl h hm p u hp hs ht ha hu hz he
    refine ⟨z,hf,?_⟩
    simpa only [hp'] using hent
  · rintro ⟨z,hz,hent⟩
    obtain ⟨S,hf,hl,h,hm,he⟩ :=
      UpperEntropyCanonical.strategy_of_feasible G (n+1) η z hz
    refine ⟨S,hf,hl,h,hm,UpperFiniteAmplitudes.pad (n+1) z.1,basis,
      UpperFiniteAmplitudes.pad_nonneg _ _ hz.1,
      UpperFiniteBorn.pad_summable _ _,
      (UpperFiniteBorn.pad_sum _ _).trans hz.2.1,
      UpperFiniteAmplitudes.pad_antitone _ _ hz.1 hz.2.2.1,
      UpperEntropyFinite.basis_orthonormal,UpperFiniteAmplitudes.pad_zero _ _,he,?_⟩
    simpa only [UpperFiniteAmplitudes.pad_fin] using hent

/-- Section 3.4, the intersection of all rational relaxations is exact feasibility. -/
theorem entropy_stage_slack (G : Game) (B n : ℕ) (η : ℚ)
    (H : ℕ → ℕ → Polynomial ℚ) (hH : EntropyApproximants H) :
    EntropyStage G B n η ↔ ∀ k,EntropyRelaxation G B n k η (H n k) := by
  rw [entropy_stage_witness,
    UpperEntropyFeasible.slack_iff G n η ((B:ℝ)+1/(n+1:ℝ)) (H n) (hH n)]
  apply forall_congr'
  intro k
  constructor
  · rintro ⟨⟨p,t,E,F⟩,hf,hent⟩
    obtain ⟨hp,hs,ha,ht,hE,hF,hEs,hFs,hl⟩ := hf
    exact ⟨p,t,E,F,hp,hs,ha,ht,hE,hF,hEs,hFs,hl,hent⟩
  · rintro ⟨p,t,E,F,hp,hs,ha,ht,hE,hF,hEs,hFs,hl,hent⟩
    exact ⟨(p,t,E,F),⟨hp,hs,ha,ht,hE,hF,hEs,hFs,hl⟩,hent⟩

/-- Finite-entropy perfection is exactly one integer budget of scheduled stages. -/
theorem entropy_scheduled_iff (G : Game) : HasFiniteEntropyPerfect G ↔
    ∃ B,∀ t,EntropyStage G B (UpperEntropySchedule.stageIndex B t) ((1/(t+1:ℚ):ℚ):ℝ) := by
  rw [UpperEntropyAssembly.scheduled_iff]
  apply exists_congr
  intro B
  unfold UpperEntropySchedule.ScheduledData
  apply forall_congr'
  intro t
  simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one] using
    (entropy_stage_witness G B (UpperEntropySchedule.stageIndex B t) (1/(t+1:ℚ))).symm

/-- Section 3.4: the effective entropy compiler and entropy-tight compactness
assemble the existential integer budget and paired universal indices. -/
theorem entropy_sigmaTwo_of_tarski (hT : UpperRealArithmetic.TarskiDecision) :
    SigmaTwo EntropyPerfect := by
  obtain ⟨coeff,hc,hH⟩ := entropy_approximants
  let H := fun n k => UpperEntropyPolynomial.polynomial (coeff (n,k+1))
  obtain ⟨R,hR,hdec⟩ := entropy_relaxation_computable_of_tarski hT
  refine ⟨fun p => R (UpperEntropyQuantifiers.decisionInput coeff p),
    hR.comp (UpperEntropyQuantifiers.decisionInput_computable coeff hc),?_⟩
  intro c
  constructor
  · rintro ⟨G,hG,hperfect⟩
    obtain ⟨B,hB⟩ := (entropy_scheduled_iff G).mp hperfect
    refine ⟨B,fun i => ?_⟩
    let t := i.unpair.1
    let k := i.unpair.2
    let n := UpperEntropySchedule.stageIndex B t
    change R (c,B,n,k,1/(t+1:ℚ),coeff (n,k+1))=true
    apply (hdec c B n k (1/(t+1:ℚ)) _).mpr
    exact ⟨G,hG,(entropy_stage_slack G B n (1/(t+1:ℚ)) H hH).mp (hB t) k⟩
  · rintro ⟨B,hB⟩
    let P (j : ℕ × ℕ) (G : Game) := EntropyRelaxation G B
      (UpperEntropySchedule.stageIndex B j.1) j.2 (1/(j.1+1:ℚ))
      (H (UpperEntropySchedule.stageIndex B j.1) j.2)
    have hall : ∀ j,GameProperty (P j) c := by
      intro j
      apply (hdec c B (UpperEntropySchedule.stageIndex B j.1) j.2 (1/(j.1+1:ℚ)) _).mp
      simpa only [UpperEntropyQuantifiers.decisionInput,Nat.unpair_pair] using
        hB (Nat.pair j.1 j.2)
    obtain ⟨G,hG,hP⟩ := (UpperEntropyQuantifiers.gameProperty_forall (0,0) P c).mpr hall
    refine ⟨G,hG,(entropy_scheduled_iff G).mpr ⟨B,fun t => ?_⟩⟩
    apply (entropy_stage_slack G B (UpperEntropySchedule.stageIndex B t) (1/(t+1:ℚ)) H hH).mpr
    intro k
    exact hP (t,k)

end Sigma2.Upper






