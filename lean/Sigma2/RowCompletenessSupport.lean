import Sigma2.RowCompletenessColumns
import Sigma2.EntropyComponentBounds

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowCompleteness
open Compiler Coefficients TensorLifts Preliminaries

/-- The original ensemble marginal annihilator kills each positive-weight vector. -/
theorem normal_left_zero {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalA S h) (A : Op) (hz : A*h.op=0)
    (k : ℕ) (hk : 0<S.weight k) : left A (S.vector k)=0 := by
  let u : ℕ × ℕ → H := fun p => column ((Real.sqrt (S.weight p.1):ℂ) • S.vector p.1) p.2
  have hu : Summable (fun p => ‖u p‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun k => (column_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).1,?_⟩
    have he (k : ℕ) : (∑' j,‖u (k,j)‖^2)=S.weight k :=
      (column_mass ((Real.sqrt (S.weight k):ℂ) • S.vector k)).2.trans
        (weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k))
    simpa only [he] using S.weight_summable
  have hs : h.op*star A=0 := by
    have he := congrArg star hz
    simp only [star_mul,h.positive.isSelfAdjoint.star_eq] at he
    exact he.trans (star_zero Op)
  have hcol (j : ℕ) : A (u (k,j))=0 := by
    apply ext_inner_left ℂ
    intro w
    rw [inner_zero_right]
    have he := congrArg (fun B : Op => B w) hs
    change h.op (star A w)=0 at he
    rw [EntropyComponentBounds.normal_marginalA_covariance S h hm] at he
    have hh := (covariance_kernel u hu (star A w)).mp he (k,j)
    exact (A.adjoint_inner_left (u (k,j)) w).symm.trans hh
  have hc : (Real.sqrt (S.weight k):ℂ)≠0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hk)
  have hzcol (j : ℕ) : A (column (S.vector k) j)=0 := by
    have he : u (k,j)=(Real.sqrt (S.weight k):ℂ) • column (S.vector k) j := by ext i; rfl
    have hh := hcol j
    rw [he,map_smul] at hh
    exact (smul_eq_zero.mp hh).resolve_left hc
  ext ⟨i,j⟩
  change (A (column (S.vector k) j)) i=0
  rw [hzcol]
  rfl

/-- The symmetric statement for Bob, on the unchanged original ensemble. -/
theorem normal_right_zero {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalB S h) (A : Op) (hz : A*h.op=0)
    (k : ℕ) (hk : 0<S.weight k) : right A (S.vector k)=0 := by
  have hh := normal_left_zero (PureTransfer.flipNormal S) h hm A hz k hk
  change left A (swap (S.vector k))=0 at hh
  have he := congrArg swap hh
  simpa only [PureTransfer.swap_left,swap_swap,map_zero] using he

theorem normal_left_support {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (k : ℕ) (hk : 0<S.weight k) : left P (S.vector k)=S.vector k := by
  have hz := normal_left_zero S h hm (1-P) (by rw [sub_mul,one_mul,hP.2.1,sub_self]) k hk
  rw [PureSupport.left_sub,left_one] at hz
  change S.vector k-left P (S.vector k)=0 at hz
  exact (sub_eq_zero.mp hz).symm

theorem normal_right_support {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalB S h) (P : Op) (hP : SupportOf h P)
    (k : ℕ) (hk : 0<S.weight k) : right P (S.vector k)=S.vector k := by
  have hz := normal_right_zero S h hm (1-P) (by rw [sub_mul,one_mul,hP.2.1,sub_self]) k hk
  rw [MagicRelations.right_sub,right_one] at hz
  change S.vector k-right P (S.vector k)=0 at hz
  exact (sub_eq_zero.mp hz).symm

/-- Compression agrees with the original reducing effect on each actual component. -/
theorem compressed_left (P A : Op) (v : AB) (hP : left P v=v) (hc : A*P=P*A) :
    left (P*A*P) v=left A v := by
  rw [← hc,left_mul,left_mul]
  change left A (left P (left P v))=left A v
  rw [hP,hP]

theorem compressed_right (P A : Op) (v : AB) (hP : right P v=v) (hc : A*P=P*A) :
    right (P*A*P) v=right A v := by
  rw [← hc,right_mul,right_mul]
  change right A (right P (right P v))=right A v
  rw [hP,hP]

/-- Named support projections are honest global projections, with every mixed
component and all original named effects retained in their action. -/
theorem compressed_named (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy G.scenario) (hR : RowsHold R S) (hN : NamedBinaryProjections R S) :
    ∃ E F : Fin R.count → Op,
      (∀ i,Projection (E i)) ∧ (∀ i,Projection (F i)) ∧
      (∀ i k,0<S.weight k →
        left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k)) ∧
      (∀ i k,0<S.weight k →
        right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k)) ∧
      (∀ i k,0<S.weight k → left (E i) (S.vector k)=right (F i) (S.vector k)) := by
  obtain ⟨hA,hB,P,Q,hmA,hmB,hP,hQ,hproj,hsync⟩ := hN
  obtain ⟨_,_,_,_,hmir,_,_⟩ := hR
  let E := fun i => P*S.measurements.alice (R.event i).x (R.event i).a*P
  let F := fun i => Q*S.measurements.bob (R.event i).y (R.event i).b*Q
  have he (i k) (hk : 0<S.weight k) :
      left (E i) (S.vector k)=S.measurements.left (R.event i).x (R.event i).a (S.vector k) := by
    rw [measurements_left]
    exact compressed_left P _ _ (normal_left_support S hA hmA P hP k hk) (hproj i).1.1
  have hf (i k) (hk : 0<S.weight k) :
      right (F i) (S.vector k)=S.measurements.right (R.event i).y (R.event i).b (S.vector k) := by
    rw [measurements_right]
    exact compressed_right Q _ _ (normal_right_support S hB hmB Q hQ k hk) (hproj i).2.1
  refine ⟨E,F,fun i => (hproj i).1.2,fun i => (hproj i).2.2,he,hf,?_⟩
  intro i k hk
  rw [he i k hk,hf i k hk]
  exact hmir i k hk

/-- Zero original ensemble events vanish on every positive-weight component. -/
theorem component_event_zero {s} (S : NormalStrategy s) (x y a b)
    (hz : S.probability x y a b=0) (k : ℕ) (hk : 0<S.weight k) :
    (S.measurements.left x a*S.measurements.right y b) (S.vector k)=0 := by
  have hn (j : ℕ) : 0 ≤ S.weight j*(S.component j).probability x y a b :=
    mul_nonneg (S.weight_nonneg j) (pure_probability_nonnegative _ _ _ _ _)
  have he := (event_summable S x y a b).le_tsum k (fun j hj => hn j)
  change S.weight k*(S.component k).probability x y a b ≤ S.probability x y a b at he
  rw [hz] at he
  have hp : (S.component k).probability x y a b=0 := by
    have hh : (S.component k).probability x y a b ≤ 0 := by
      by_contra hp
      exact (not_lt_of_ge he) (mul_pos hk (lt_of_not_ge hp))
    exact le_antisymm hh (pure_probability_nonnegative _ _ _ _ _)
  apply positive_apply_eq_zero _ (S.measurements.joint_positive x y a b)
  exact hp

end Sigma2.RowCompleteness
