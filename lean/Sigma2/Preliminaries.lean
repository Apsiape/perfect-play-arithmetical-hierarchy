import Sigma2.TraceProducts
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

noncomputable section
open scoped BigOperators
namespace Sigma2.Preliminaries

theorem positive_apply_eq_zero {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (hT : T.IsPositive)
    (v : E) (hz : (inner ℂ v (T v)).re=0) : T v=0 := by
  let := InnerProductSpace.rclikeToReal ℂ E
  let A := T.restrictScalars ℝ
  let a : ℝ := inner ℝ (A v) (A (A v))
  let b : ℝ := ‖A v‖^2
  have hpos (x : E) : 0 ≤ inner ℝ x (A x) := hT.re_inner_nonneg_right x
  have ha : 0 ≤ a := hpos _
  have hb : 0 ≤ b := sq_nonneg _
  have hz' : inner ℝ v (A v)=0 := hz
  have hcross : inner ℝ v (A (A v))=b := by
    calc
      _ = inner ℝ (A v) (A v) := congrArg RCLike.re (hT.isSymmetric v (T v)).symm
      _ = b := real_inner_self_eq_norm_sq _
  have hpoly (r : ℝ) : 0 ≤ r^2*a-2*r*b := by
    have h := hpos (v-r • A v)
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
      real_inner_smul_left, real_inner_smul_right, hz', hcross,
      real_inner_self_eq_norm_sq] at h
    change 0 ≤ 0-r*b-(r*b-r*(r*a)) at h
    nlinarith
  have hb0 : b=0 := by
    by_contra hn
    have hbpos : 0<b := lt_of_le_of_ne hb (Ne.symm hn)
    let r := b/(a+1)
    have hr : 0<r := div_pos hbpos (by linarith)
    have hre : r*(a+1)=b := div_mul_cancel₀ _ (by linarith)
    have hp := hpoly r
    nlinarith [mul_nonneg (sq_nonneg r) ha, sq_pos_of_pos hr]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hb0)

theorem positive_compression_zero (B P : Op) (hB : Positive B)
    (hP : Projection P) (hz : P*B*P=0) : B*P=0 := by
  have hs : P.IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP.1
  apply ContinuousLinearMap.ext
  intro v
  change B (P v)=0
  apply positive_apply_eq_zero B hB
  have heq : inner ℂ (P v) (B (P v))=inner ℂ v ((P*B*P) v) := by
    exact hs v (B (P v))
  rw [heq, hz]
  simp

theorem positive_below_projection (B P : Op) (hB : Positive B)
    (hP : Projection P) (hPB : Positive (P-B)) : B*P=B ∧ P*B=B := by
  have hsB : star B=B := hB.isSelfAdjoint
  have hn : B*(1-P)=0 := by
    apply ContinuousLinearMap.ext
    intro v
    change B ((1-P) v)=0
    apply positive_apply_eq_zero B hB
    have hp := hB.re_inner_nonneg_right ((1-P) v)
    have hq := hPB.re_inner_nonneg_right ((1-P) v)
    have hzero : P*((1-P):Op)=0 := by rw [mul_sub, mul_one, hP.2, sub_self]
    have heq : (P-B) ((1-P) v) = -B ((1-P) v) := by
      have hh := congrArg (fun L : Op => L v) hzero
      change P ((1-P) v)=0 at hh
      rw [sub_apply, hh, zero_sub]
    rw [heq, inner_neg_right, map_neg] at hq
    change 0 ≤ (inner ℂ ((1-P) v) (B ((1-P) v))).re at hp
    change 0 ≤ -(inner ℂ ((1-P) v) (B ((1-P) v))).re at hq
    linarith
  have hr : B*P=B := by
    rw [mul_sub, mul_one] at hn
    exact (sub_eq_zero.mp hn).symm
  refine ⟨hr, ?_⟩
  have hh := congrArg (fun L : Op => star L) hr
  simpa only [star_mul, hsB, hP.1] using hh

theorem positive_sum_erase {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → Op) (hA : ∀ i, Positive (A i)) (i : ι) :
    Positive ((∑ j, A j)-A i) := by
  have heq : (∑ j, A j)-A i=∑ j ∈ Finset.univ.erase i, A j := by
    exact sub_eq_iff_eq_add.mpr (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  rw [heq]
  exact ContinuousLinearMap.isPositive_sum _ (fun j _ => hA j)


/-- Scalar matrix coefficients of a normal state's trace-class density on AB. -/
structure BipDensity where
  op : BipOp
  positive : op.IsPositive
  summable : Summable (fun ij : ℕ × ℕ =>
    (inner ℂ (lp.single 2 ij (1 : ℂ)) (op (lp.single 2 ij (1 : ℂ)))).re)
  trace_one : (∑' ij : ℕ × ℕ,
    (inner ℂ (lp.single 2 ij (1 : ℂ)) (op (lp.single 2 ij (1 : ℂ)))).re) = 1

def Represents {s} (ρ : BipDensity) (S : NormalStrategy s) : Prop :=
  ∀ v w : AB, inner ℂ v (ρ.op w) =
    ∑' k, (S.weight k : ℂ) * inner ℂ v (S.vector k) * inner ℂ (S.vector k) w

/-- Normal-state model equivalence, spectral theorem for positive trace class.
Own foundational obligation; no theorem of either Douglas--Mghirbi paper is assumed. -/
theorem density_ensemble_equivalence (s : Scenario) (M : Measurements s) :
    (∀ ρ : BipDensity, ∃ S : NormalStrategy s, S.measurements = M ∧ Represents ρ S) ∧
    (∀ S : NormalStrategy s, ∃ ρ : BipDensity, Represents ρ S) := by
  classical
  constructor
  · intro ρ
    let e : ℕ ≃ ℕ × ℕ := Nat.pairEquiv.symm
    let u : ℕ → AB := fun k => Coefficients.positiveRoot ρ.op (lp.single 2 (e k) 1)
    have hmass k : ‖u k‖^2 =
        (inner ℂ (lp.single 2 (e k) 1) (ρ.op (lp.single 2 (e k) 1))).re :=
      Coefficients.sqrt_column_norm_sq ρ.op ρ.positive (e k)
    have hu : Summable (fun k => ‖u k‖^2) := by
      simp_rw [hmass]
      exact e.summable_iff.mpr ρ.summable
    have hsum : (∑' k, ‖u k‖^2)=1 := by
      simp_rw [hmass]
      exact (e.tsum_eq (fun ij =>
        (inner ℂ (lp.single 2 ij 1) (ρ.op (lp.single 2 ij 1))).re)).trans ρ.trace_one
    let S : NormalStrategy s := {
      measurements := M
      vector := fun k => Coefficients.unitVector (u k)
      unit := fun k => Coefficients.unitVector_unit (u k)
      weight := fun k => ‖u k‖^2
      weight_nonneg := fun k => sq_nonneg _
      weight_summable := hu
      weight_sum := hsum }
    refine ⟨S,rfl,?_⟩
    intro v w
    change inner ℂ v (ρ.op w) = ∑' k, ((‖u k‖^2:ℝ):ℂ)*
      inner ℂ v (Coefficients.unitVector (u k))*inner ℂ (Coefficients.unitVector (u k)) w
    simp_rw [Coefficients.unitVector_coefficient]
    exact ((e.hasSum_iff).mpr (Coefficients.sqrt_columns ρ.op ρ.positive v w)).tsum_eq.symm
  · intro S
    let u : ℕ → AB := fun k => (Real.sqrt (S.weight k):ℂ) • S.vector k
    have hmass k : ‖u k‖^2=S.weight k :=
      Coefficients.weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k)
    have hu : Summable (fun k => ‖u k‖^2) := by
      simpa only [hmass] using S.weight_summable
    have ht := Coefficients.covariance_trace u hu
    let ρ : BipDensity := {
      op := Coefficients.covariance u
      positive := Coefficients.covariance_positive u
      summable := by simpa [lp.inner_single_left,RCLike.inner_apply] using ht.1
      trace_one := by
        simpa only [lp.inner_single_left,RCLike.inner_apply,map_one,one_mul,mul_one,hmass,S.weight_sum]
          using ht.2 }
    refine ⟨ρ,?_⟩
    intro v w
    have hh := (Coefficients.covariance_hasSum u hu v w).tsum_eq.symm
    simpa only [u,Coefficients.weighted_coefficient _ (S.weight_nonneg _)] using hh

/-- Every positive trace-class density has a closed state support on which it
is faithful. This makes the bridge statement cover finite supports as well. -/
def SupportOf (h : Density) (e : Op) : Prop :=
  Projection e ∧ e*h.op=h.op ∧ ∀ v,e v=v → h.op v=0 → v=0

theorem support_exists (h : Density) : ∃ e : Op,SupportOf h e := by
  let K := h.op.ker
  let e : Op := Kᗮ.starProjection
  refine ⟨e, ⟨?_, ?_⟩, ?_, ?_⟩
  · exact isSelfAdjoint_starProjection _
  · exact Submodule.isIdempotentElem_starProjection _
  · apply ContinuousLinearMap.ext
    intro v
    change Kᗮ.starProjection (h.op v) = h.op v
    apply Submodule.starProjection_eq_self_iff.mpr
    intro w hw
    calc
      _ = inner ℂ (h.op w) v := (h.positive.isSymmetric w v).symm
      _ = 0 := by
        change h.op w=0 at hw
        simp [hw]
  · intro v hv hz
    have hvK : v ∈ K := hz
    have hvO : v ∈ Kᗮ := Submodule.starProjection_eq_self_iff.mp hv
    exact (inner_self_eq_zero (𝕜 := ℂ)).mp (hvO v hvK)

/-- Separable Hilbert spaces embed isometrically in the fixed countable model.
Finite-dimensional spaces use a closed proper support; no infinite-rank
faithfulness is silently imposed on a finite strategy. -/
theorem separable_hilbert_embedding (E : Type) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E] :
    Nonempty (E →ₗᵢ[ℂ] H) := by
  exact Coefficients.separable_embedding E

/-- All bounded local POVMs have the concrete tensor lifts required in Statements. -/
theorem tensor_lifts_exist (s : Scenario)
    (E : QA s → AA s → Op) (F : QB s → BB s → Op)
    (hE : ∀ x a, Positive (E x a)) (hF : ∀ y b, Positive (F y b))
    (sE : ∀ x, ∑ a, E x a = 1) (sF : ∀ y, ∑ b, F y b = 1) :
    ∃ M : Measurements s, M.alice = E ∧ M.bob = F := by
  exact ⟨TensorLifts.measurements s E F hE hF sE sF,rfl,rfl⟩

/-- Explicit purification equivalence: the countable environment is absorbed into
Alice's separable local factor, N x N is reindexed to N, and all events agree. -/
theorem purification {s} (S : NormalStrategy s) :
    ∃ T : PureStrategy s, ∀ x y a b,
      S.probability x y a b = T.probability x y a b := by
  exact Purification.exists_pure S

theorem purified_model_equivalence : PurifiedModelEquivalence := by
  intro s
  refine ⟨purification,?_⟩
  intro T
  exact ⟨normalOfPure T,normalOfPure_probability T⟩

theorem normal_pure_perfect_equivalence (G : Game) :
    HasPerfect G ↔ ∃ T : PureStrategy G.scenario,Perfect G (normalOfPure T) := by
  constructor
  · rintro ⟨S,hS⟩
    obtain ⟨T,hT⟩ := purification S
    refine ⟨T,?_⟩
    have heq : loss G S=loss G (normalOfPure T) := by
      simp only [loss,normalOfPure_probability]
      simp_rw [hT]
    change loss G (normalOfPure T)=0
    rw [← heq]
    exact hS
  · rintro ⟨T,hT⟩;exact ⟨normalOfPure T,hT⟩

theorem marginals_exist {s} (S : NormalStrategy s) :
    ∃ hA hB : Density,MarginalA S hA ∧ MarginalB S hB := by
  classical
  let w : ℕ → AB := fun k => (Real.sqrt (S.weight k):ℂ) • S.vector k
  have hw k : ‖w k‖^2=S.weight k :=
    Coefficients.weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k)
  let uA : ℕ × ℕ → H := fun kb => Coefficients.column (w kb.1) kb.2
  let uB : ℕ × ℕ → H := fun ka => Coefficients.row (w ka.1) ka.2
  have hA : Summable (fun kb => ‖uA kb‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun k => (Coefficients.column_mass (w k)).1, ?_⟩
    simpa only [uA,(Coefficients.column_mass _).2,hw] using S.weight_summable
  have hB : Summable (fun ka => ‖uB ka‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun k => (Coefficients.row_mass (w k)).1, ?_⟩
    simpa only [uB,(Coefficients.row_mass _).2,hw] using S.weight_summable
  have hsumA : (∑' kb, ‖uA kb‖^2)=1 := by
    rw [hA.tsum_prod]
    simp only [uA,(Coefficients.column_mass _).2,hw,S.weight_sum]
  have hsumB : (∑' ka, ‖uB ka‖^2)=1 := by
    rw [hB.tsum_prod]
    simp only [uB,(Coefficients.row_mass _).2,hw,S.weight_sum]
  have mk (u : ℕ × ℕ → H) (hu : Summable (fun k => ‖u k‖^2))
      (hsum : (∑' k, ‖u k‖^2)=1) : ∃ h : Density, h.op=Coefficients.covariance u := by
    have ht := Coefficients.covariance_trace u hu
    refine ⟨⟨Coefficients.covariance u,Coefficients.covariance_positive u,?_,?_⟩,rfl⟩
    · simpa only [entry,basis] using ht.1
    · simpa only [entry,basis] using ht.2.trans hsum
  obtain ⟨ρA,hρA⟩ := mk uA hA hsumA
  obtain ⟨ρB,hρB⟩ := mk uB hB hsumB
  refine ⟨ρA,ρB,?_,?_⟩
  · intro i j
    unfold entry
    rw [hρA]
    simp only [basis]
    rw [Coefficients.covariance_entry uA hA i j]
    rw [(Coefficients.coefficient_summable uA hA i j).tsum_prod]
    apply tsum_congr
    intro k
    simp only [uA,Coefficients.column_apply,w]
    simp_rw [Coefficients.weighted_entry _ (S.weight_nonneg k),tsum_mul_left]
  · intro i j
    unfold entry
    rw [hρB]
    simp only [basis]
    rw [Coefficients.covariance_entry uB hB i j]
    rw [(Coefficients.coefficient_summable uB hB i j).tsum_prod]
    apply tsum_congr
    intro k
    simp only [uB,Coefficients.row_apply,w]
    simp_rw [Coefficients.weighted_entry _ (S.weight_nonneg k),tsum_mul_left]

theorem complex_re_sum {ι : Type} (t : Finset ι) (f : ι → ℂ) :
    (∑ i ∈ t, f i).re=∑ i ∈ t, (f i).re := map_sum Complex.reCLM f t

theorem pure_probability_nonnegative {s} (S : PureStrategy s) (x y a b) :
    0 ≤ S.probability x y a b :=
  (S.measurements.joint_positive x y a b).re_inner_nonneg_right _

theorem pure_probability_normalized {s} (S : PureStrategy s) (x y) :
    ∑ a, ∑ b, S.probability x y a b=1 := by
  have hop : (∑ a,∑ b,S.measurements.left x a*S.measurements.right y b)=1 := by
    simp_rw [← Finset.mul_sum,S.measurements.right_sum,mul_one]
    exact S.measurements.left_sum x
  have h := congrArg (fun L : BipOp => (inner ℂ S.vector (L S.vector)).re) hop
  simp only [sum_apply, inner_sum, complex_re_sum, one_apply_eq_self,
    inner_self_eq_norm_sq_to_K, S.unit] at h
  convert h using 1 <;> norm_num [PureStrategy.probability]

theorem pure_probability_le_one {s} (S : PureStrategy s) (x y a b) :
    S.probability x y a b≤1 := by
  calc
    _ ≤ ∑ b',S.probability x y a b' := Finset.single_le_sum
      (fun b' _ => pure_probability_nonnegative S x y a b') (Finset.mem_univ b)
    _ ≤ ∑ a',∑ b',S.probability x y a' b' := Finset.single_le_sum
      (fun a' _ => Finset.sum_nonneg fun b' _ => pure_probability_nonnegative S x y a' b')
      (Finset.mem_univ a)
    _ = 1 := pure_probability_normalized S x y

theorem event_summable {s} (S : NormalStrategy s) (x y a b) :
    Summable (fun k => S.weight k*(S.component k).probability x y a b) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (S.weight_nonneg k) (pure_probability_nonnegative _ _ _ _ _))
    (fun k => ?_) S.weight_summable
  exact mul_le_of_le_one_right (S.weight_nonneg k) (pure_probability_le_one _ _ _ _ _)

theorem probability_nonnegative {s} (S : NormalStrategy s) (x y a b) :
    0 ≤ S.probability x y a b := by
  exact tsum_nonneg (fun k => mul_nonneg (S.weight_nonneg k)
    ((S.measurements.joint_positive x y a b).re_inner_nonneg_right (S.vector k)))

theorem probability_normalized {s} (S : NormalStrategy s) (x y) :
    ∑ a, ∑ b, S.probability x y a b = 1 := by
  unfold NormalStrategy.probability
  have hin a : (∑ b,∑' k,S.weight k*(S.component k).probability x y a b)=
      ∑' k,∑ b,S.weight k*(S.component k).probability x y a b :=
    (Summable.tsum_finsetSum (s:=Finset.univ) (fun b _ => event_summable S x y a b)).symm
  simp_rw [hin]
  rw [← Summable.tsum_finsetSum (s:=Finset.univ)
    (fun a _ => summable_sum (s:=Finset.univ) (fun b _ => event_summable S x y a b))]
  simp_rw [← Finset.mul_sum,pure_probability_normalized,mul_one]
  exact S.weight_sum

theorem loss_eq_one_sub_win (G : Game) (S : NormalStrategy G.scenario) :
    loss G S = 1 - win G S := by
  apply eq_sub_iff_add_eq.mpr
  calc
    loss G S+win G S = ∑ x,∑ y,∑ a,∑ b,
        (G.distribution x y:ℝ)*S.probability x y a b := by
      unfold loss win
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro y _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro a _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro b _
      cases G.accepts x y a b <;> simp
    _ = ∑ x,∑ y,(G.distribution x y:ℝ) := by
      simp_rw [← Finset.mul_sum,probability_normalized,mul_one]
    _ = 1 := by exact_mod_cast G.distribution_sum

theorem losing_event_le_loss (G : Game) (S : NormalStrategy G.scenario) (x y a b) :
    (G.distribution x y:ℝ)*(if G.accepts x y a b then 0 else S.probability x y a b) ≤ loss G S := by
  have hn x y a b : 0 ≤ (G.distribution x y:ℝ)*
      (if G.accepts x y a b then 0 else S.probability x y a b) :=
    mul_nonneg (by exact_mod_cast G.distribution_nonneg x y)
      (by split <;> simp_all [probability_nonnegative])
  unfold loss
  calc
    _ ≤ ∑ b', (G.distribution x y:ℝ)*(if G.accepts x y a b' then 0 else S.probability x y a b') :=
      Finset.single_le_sum (fun b' _ => hn x y a b') (Finset.mem_univ b)
    _ ≤ ∑ a',∑ b', (G.distribution x y:ℝ)*(if G.accepts x y a' b' then 0 else S.probability x y a' b') :=
      Finset.single_le_sum (fun a' _ => Finset.sum_nonneg fun b' _ => hn x y a' b') (Finset.mem_univ a)
    _ ≤ ∑ y',∑ a',∑ b', (G.distribution x y':ℝ)*(if G.accepts x y' a' b' then 0 else S.probability x y' a' b') :=
      Finset.single_le_sum (fun y' _ => Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ => hn x y' a' b') (Finset.mem_univ y)
    _ ≤ _ := Finset.single_le_sum (fun x' _ => Finset.sum_nonneg fun y' _ =>
      Finset.sum_nonneg fun a' _ => Finset.sum_nonneg fun b' _ => hn x' y' a' b') (Finset.mem_univ x)

/-- Fact 2.1: every positive-weight component of a perfect normal strategy is perfect. -/
theorem fact_2_1_pure_components (G : Game) (S : NormalStrategy G.scenario)
    (hS : Perfect G S) (k : ℕ) (hk : 0 < S.weight k) :
    Perfect G (normalOfPure (S.component k)) := by
  unfold Perfect loss
  simp_rw [normalOfPure_probability]
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro y _
  apply Finset.sum_eq_zero; intro a _
  apply Finset.sum_eq_zero; intro b _
  cases ha : G.accepts x y a b
  · simp only [Bool.false_eq_true,ite_false]
    have hd : 0≤(G.distribution x y:ℝ) := by exact_mod_cast G.distribution_nonneg x y
    have hp := (event_summable S x y a b).le_tsum k (fun j _ =>
      mul_nonneg (S.weight_nonneg j) (pure_probability_nonnegative _ _ _ _ _))
    have hb := losing_event_le_loss G S x y a b
    simp only [ha,Bool.false_eq_true,ite_false] at hb
    rw [hS] at hb
    have hz : S.weight k*((G.distribution x y:ℝ)*(S.component k).probability x y a b)≤0 := by
      calc
        _ = (G.distribution x y:ℝ)*(S.weight k*(S.component k).probability x y a b) := by ring
        _ ≤ (G.distribution x y:ℝ)*S.probability x y a b := mul_le_mul_of_nonneg_left hp hd
        _ ≤ 0 := hb
    exact le_antisymm (le_of_not_gt (fun hp => (not_lt_of_ge hz) (mul_pos hk hp)))
      (mul_nonneg hd (pure_probability_nonnegative _ _ _ _ _))
  · simp [ha]

def weightedTrace (h : Density) (T : Op) : ℝ := (trace (h.op * T)).re

/-- Fact 2.2 / entropy-paper support: faithfulness detects zero positive operators. -/
theorem faithful_positive_zero (h : Density) (hh : Faithful h) (B : Op)
    (hB : Positive B) (hz : weightedTrace h B = 0) : B = 0 := by
  have hz' := TraceProducts.zero_trace_columns h B hB hz
  have hcol k : B (TraceProducts.rootFamily h k)=0 := by
    apply positive_apply_eq_zero B hB
    calc
      _ = (inner ℂ (B (TraceProducts.rootFamily h k)) (TraceProducts.rootFamily h k)).re :=
        congrArg Complex.re (hB.isSymmetric _ _).symm
      _ = 0 := hz' k
  apply ContinuousLinearMap.ext
  intro v
  apply hh
  change h.op (B v)=h.op (0:H)
  rw [map_zero,TraceProducts.density_eq_covariance]
  apply (Coefficients.covariance_kernel _ (TraceProducts.root_summable h) (B v)).mpr
  intro k
  calc
    _ = inner ℂ v (B (TraceProducts.rootFamily h k)) := hB.isSymmetric _ _
    _ = 0 := by rw [hcol k,inner_zero_right]

theorem positive_defect (E : BipOp) (hE : E.IsPositive) (hE' : (1-E).IsPositive) :
    (E-E*E).IsPositive := by
  have h0 : 0 ≤ E := ContinuousLinearMap.nonneg_iff_isPositive.mpr hE
  have h1 : E ≤ 1 := hE'
  exact CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one h0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg E h0).mpr h1)

/-- Fact 2.2: the zero-mismatch decomposition on the actual purification. -/
theorem matching_on_vector (E F : BipOp) (Ω : AB)
    (hE : E.IsPositive) (hE' : (1-E).IsPositive)
    (hF : F.IsPositive) (hF' : (1-F).IsPositive)
    (hcomm : E*F=F*E)
    (hz : (inner ℂ Ω ((E+F-(2:ℂ) • (E*F)) Ω)).re=0) :
    E Ω = F Ω ∧ (E-E*E) Ω=0 ∧ (F-F*F) Ω=0 := by
  have hdE := positive_defect E hE hE'
  have hdF := positive_defect F hF hF'
  have hsym : star (E-F)=E-F := hE.isSelfAdjoint.sub hF.isSelfAdjoint
  have hd : ((E-F)*(E-F)).IsPositive := by
    have h := ContinuousLinearMap.isPositive_adjoint_comp_self (E-F)
    change ((star (E-F))*(E-F)).IsPositive at h
    rwa [hsym] at h
  have heq : E+F-(2:ℂ) • (E*F)=(E-F)*(E-F)+(E-E*E)+(F-F*F) := by
    rw [sub_mul,mul_sub,mul_sub,← hcomm]
    module
  rw [heq] at hz
  simp only [add_apply,inner_add_right,Complex.add_re] at hz
  have hnD := hd.re_inner_nonneg_right Ω
  have hnE := hdE.re_inner_nonneg_right Ω
  have hnF := hdF.re_inner_nonneg_right Ω
  change 0 ≤ (inner ℂ Ω (((E-F)*(E-F)) Ω)).re at hnD
  change 0 ≤ (inner ℂ Ω ((E-E*E) Ω)).re at hnE
  change 0 ≤ (inner ℂ Ω ((F-F*F) Ω)).re at hnF
  have hD : (inner ℂ Ω (((E-F)*(E-F)) Ω)).re=0 := by linarith
  have hDE : (inner ℂ Ω ((E-E*E) Ω)).re=0 := by linarith
  have hDF : (inner ℂ Ω ((F-F*F) Ω)).re=0 := by linarith
  refine ⟨?_,positive_apply_eq_zero _ hdE Ω hDE,positive_apply_eq_zero _ hdF Ω hDF⟩
  have hi : inner ℂ ((E-F) Ω) ((E-F) Ω)=0 := by
    have hv := positive_apply_eq_zero _ hd Ω hD
    have hs : (E-F).IsSymmetric := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsym
    calc
      _ = inner ℂ Ω ((E-F) ((E-F) Ω)) := hs Ω ((E-F) Ω)
      _ = 0 := by change inner ℂ Ω (((E-F)*(E-F)) Ω)=0; rw [hv,inner_zero_right]
  have h0 := (inner_self_eq_zero (𝕜 := ℂ)).mp hi
  exact sub_eq_zero.mp (by simpa using h0)

/-- Fact 2.3 / entropy support, projectivity is used after compression. -/
theorem sharp_compression (P E : Op) (hP : Projection P)
    (hE : PositiveContraction E) (hsharp : Projection (P*E*P)) :
    E*P=P*E := by
  let Q := P*E*P
  have hPQ : P*Q=Q := by simp only [Q, ← mul_assoc, hP.2]
  have hQP : Q*P=Q := by simp only [Q, mul_assoc, hP.2]
  have hQQ : Q*Q=Q := hsharp.2
  have hsQ : star Q=Q := hsharp.1
  have hPcQ : Projection (P-Q) := by
    constructor
    · exact (star_sub P Q).trans (congrArg₂ (fun X Y : Op => X-Y) hP.1 hsQ)
    · simp only [sub_mul, mul_sub, hP.2, hPQ, hQP, hQQ]; abel
  have hQE : Q*E*Q=Q := by
    calc
      _ = (Q*P)*E*(P*Q) := by rw [hQP, hPQ]
      _ = Q*(P*E*P)*Q := by noncomm_ring
      _ = Q := by change Q*Q*Q=Q; rw [hQQ, hQQ]
  have hEQ : (1-E)*Q=0 := positive_compression_zero _ _ hE.2 hsharp (by
    rw [mul_sub, mul_one, sub_mul, hQQ, hQE, sub_self])
  have hEc : E*(P-Q)=0 := positive_compression_zero _ _ hE.1 hPcQ (by
    calc
      _ = ((P-Q)*P)*E*(P*(P-Q)) := by
        have h1 : (P-Q)*P=P-Q := by rw [sub_mul, hP.2, hQP]
        have h2 : P*(P-Q)=P-Q := by rw [mul_sub, hP.2, hPQ]
        rw [h1,h2]
      _ = (P-Q)*Q*(P-Q) := by dsimp [Q]; noncomm_ring
      _ = 0 := by simp only [sub_mul, mul_sub, hPQ, hQP, hQQ]; abel)
  have hEP : E*P=Q := by
    rw [sub_mul, one_mul] at hEQ
    rw [mul_sub] at hEc
    have h1 := sub_eq_zero.mp hEQ
    have h2 := sub_eq_zero.mp hEc
    exact h2.trans h1.symm
  have hh := congrArg (fun L : Op => star L) hEP
  have hPE : P*E=Q := by
    simpa only [star_mul, hP.1, hE.1.isSelfAdjoint.star_eq, hsQ] using hh
  exact hEP.trans hPE.symm

/-- Fact 2.3: a joint POVM with sharp marginals is the joint spectral measurement. -/
theorem sharp_joint {m n : ℕ} (Q : Fin m → Fin n → Op)
    (hQ : ∀ i j, Positive (Q i j)) (hs : ∑ i, ∑ j, Q i j=1)
    (hA : ∀ i, Projection (∑ j, Q i j))
    (hB : ∀ j, Projection (∑ i, Q i j)) :
    ∀ i j, Q i j = (∑ b, Q i b)*(∑ a, Q a j) := by
  have hr i j := positive_below_projection (Q i j) (∑ b, Q i b)
    (hQ i j) (hA i) (positive_sum_erase _ (hQ i) j)
  have hc i j := positive_below_projection (Q i j) (∑ a, Q a j)
    (hQ i j) (hB j) (positive_sum_erase _ (fun a => hQ a j) i)
  have hrows i : Positive (1-(∑ b, Q i b)) := by
    rw [← hs]
    exact positive_sum_erase _ (fun a => ContinuousLinearMap.isPositive_sum _ (fun b _ => hQ a b)) i
  have horth i a (hne : a≠i) : (∑ b, Q i b)*(∑ b, Q a b)=0 := by
    have hz : (∑ b, Q a b)*(∑ b, Q i b)=0 := by
      have hdom : Positive ((1-∑ b, Q i b)-(∑ b, Q a b)) := by
        have heq : (1-∑ b, Q i b)-(∑ b, Q a b)=
            ∑ k ∈ (Finset.univ.erase i).erase a, ∑ b, Q k b := by
          have h1 := Finset.sum_erase_add Finset.univ (fun k => ∑ b, Q k b) (Finset.mem_univ i)
          have h2 := Finset.sum_erase_add (Finset.univ.erase i) (fun k => ∑ b, Q k b)
            (Finset.mem_erase.mpr ⟨hne,Finset.mem_univ a⟩)
          rw [hs] at h1
          rw [← h1, ← h2]
          abel
        rw [heq]
        exact ContinuousLinearMap.isPositive_sum _ (fun k _ =>
          ContinuousLinearMap.isPositive_sum _ (fun b _ => hQ k b))
      have hcompl : Projection (1-∑ b, Q i b) := by
        constructor
        · exact (star_sub _ _).trans (congrArg₂ (fun X Y : Op => X-Y) (star_one _) (hA i).1)
        · simp only [sub_mul, mul_sub, one_mul, mul_one, (hA i).2]; abel
      have hh := (positive_below_projection (∑ b, Q a b) _
        (ContinuousLinearMap.isPositive_sum _ (fun b _ => hQ a b)) hcompl hdom).1
      rw [mul_sub, mul_one] at hh
      exact sub_eq_self.mp hh
    have hh := congrArg (fun L : Op => star L) hz
    rw [star_mul, (hA a).1, (hA i).1] at hh
    exact hh.trans (star_zero Op)
  intro i j
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · exact (hr i j).2.symm
  · intro a _ hne
    calc
      (∑ b, Q i b)*Q a j = (∑ b, Q i b)*((∑ b, Q a b)*Q a j) := by rw [(hr a j).2]
      _ = 0 := by rw [← mul_assoc, horth i a hne, zero_mul]
  · simp

/-- Fact 2.4: dense coefficient range turns a vector forbidden event into a local identity.
This is the central dense-range cancellation, independent of any inverse density bound. -/
theorem dense_range_cancel (B T : Op) (hT : DenseRange T) (hz : B*T=0) : B=0 := by
  apply ContinuousLinearMap.ext
  intro v
  have heq : B ∘ T = (0 : H →L[ℂ] H) ∘ T := by
    funext u
    have h := congrArg (fun L : Op => L u) hz
    simpa using h
  exact congrFun (hT.equalizer B.continuous (0 : H →L[ℂ] H).continuous heq) v

theorem fact_2_4_forbidden (Q K T : Op) (hT : DenseRange T) (hz : (Q*K)*T=0) :
    Q*K=0 := dense_range_cancel (Q*K) T hT hz

end Sigma2.Preliminaries
