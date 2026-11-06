import Sigma2.MatrixSupportCoordinates
import Sigma2.TraceProducts

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.MatrixSupportCoordinates
open Preliminaries Coefficients TraceProducts

/-- Transport of an actual trace-class density, proved by its summable
rank-one family. No operator-norm continuity of trace is used. -/
theorem sandwich_covariance (h : Density) (B : Op) :
    B*h.op*star B=covariance (fun k => B (rootFamily h k)) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  have hh := covariance_hasSum (fun k => B (rootFamily h k))
    (image_summable B _ (root_summable h)) w v
  have hk := covariance_hasSum (rootFamily h) (root_summable h) (star B w) (star B v)
  rw [← density_eq_covariance h] at hk
  have he (k : ℕ) : inner ℂ w (B (rootFamily h k))*inner ℂ (B (rootFamily h k)) v=
      inner ℂ (star B w) (rootFamily h k)*inner ℂ (rootFamily h k) (star B v) := by
    simp only [ContinuousLinearMap.star_eq_adjoint]
    rw [B.adjoint_inner_left,B.adjoint_inner_right]
  have hf := hh.tsum_eq.symm.trans ((tsum_congr he).trans hk.tsum_eq)
  simpa only [mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left] using hf.symm

theorem sandwich_trace (h : Density) (B : Op) :
    trace (B*h.op*star B)=trace (h.op*(star B*B)) := by
  have hp : Positive (star B*B) := by
    exact ContinuousLinearMap.nonneg_iff_isPositive.mp (star_mul_self_nonneg B)
  have ht := covariance_mul_trace (rootFamily h) (root_summable h) (star B*B) hp
  rw [← density_eq_covariance h] at ht
  rw [sandwich_covariance h B]
  have hleft := covariance_mul_trace (fun k => B (rootFamily h k))
    (image_summable B _ (root_summable h)) 1 ContinuousLinearMap.isPositive_one
  rw [mul_one] at hleft
  rw [hleft.2.1,ht.2.1]
  apply tsum_congr
  intro k
  simp only [one_apply_eq_self,mul_apply_eq_comp]
  exact (B.adjoint_inner_left _ _).symm

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {P : Op} {t : ι → ι → Op}
namespace Units

theorem diagonal_projection (hu : Units P t) (i : ι) : Projection (t i i) :=
  ⟨hu.adjoint i i,by rw [hu.product,if_pos rfl]⟩

theorem diagonal_positive (hu : Units P t) (i : ι) : Positive (t i i) := by
  have hh : star (t i i)*t i i=t i i := by rw [hu.adjoint,hu.product,if_pos rfl]
  rw [← hh]
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp (star_mul_self_nonneg _)

theorem density_diagonal_summable (hu : Units P t) (h : Density) (i : ι) :
    Summable (fun k => (entry (h.op*t i i) k k).re) := by
  have ht := covariance_mul_trace (rootFamily h) (root_summable h) (t i i) (hu.diagonal_positive i)
  rw [← density_eq_covariance h] at ht
  exact (ht.1.hasSum.mapL Complex.reCLM).summable

/-- All scalar corners have the same actual trace. -/
theorem corner_trace_equal (hu : Units P t) (h : Density)
    (hc : ∀ i j,Commute h.op (t i j)) (o i : ι) :
    trace (h.op*t o o)=trace (h.op*t i i) := by
  have he : t o i*h.op*star (t o i)=h.op*t o o := by
    rw [← (hc o i).eq,mul_assoc,hu.adjoint,hu.product,if_pos rfl]
  have hf := sandwich_trace h (t o i)
  rw [he,hu.adjoint,hu.product,if_pos rfl] at hf
  exact hf

/-- Trace-one normalization of the corner, with the correct dimension factor. -/
theorem corner_mass (hu : Units P t) (h : Density) (hP : SupportOf h P)
    (hc : ∀ i j,Commute h.op (t i j)) (o : ι) :
    (Fintype.card ι:ℝ)*(∑' k,(entry (h.op*t o o) k k).re)=1 := by
  have he (i : ι) : (∑' k,(entry (h.op*t i i) k k).re)=
      ∑' k,(entry (h.op*t o o) k k).re := by
    have hh := congrArg Complex.re (hu.corner_trace_equal h hc o i)
    have hi := covariance_mul_trace (rootFamily h) (root_summable h) (t i i) (hu.diagonal_positive i)
    have ho := covariance_mul_trace (rootFamily h) (root_summable h) (t o o) (hu.diagonal_positive o)
    rw [← density_eq_covariance h] at hi ho
    simpa only [trace,Complex.re_tsum hi.1,Complex.re_tsum ho.1] using hh.symm
  have hsum : (∑ i,∑' k,(entry (h.op*t i i) k k).re)=1 := by
    rw [← Summable.tsum_finsetSum (fun i _ => hu.density_diagonal_summable h i)]
    have hp := MatrixCentralizer.support_centralizes h P hP
    have hright : h.op*P=h.op := hp.eq.trans hP.2.1
    have hx (k : ℕ) : (∑ i,(entry (h.op*t i i) k k).re)=(entry h.op k k).re := by
      rw [← Complex.re_sum]
      congr 1
      have hh := congrArg (fun A : Op => A (basis k) k)
        (show (∑ i,h.op*t i i)=h.op by rw [← Finset.mul_sum,hu.total,hright])
      simpa only [entry,sum_apply,lp.coeFn_sum,Finset.sum_apply] using hh
    simpa only [hx] using h.trace_one
  simpa only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using hsum

def cornerDensity (hu : Units P t) (h : Density) (hP : SupportOf h P)
    (hc : ∀ i j,Commute h.op (t i j)) (o : ι) : Density where
  op := (Fintype.card ι:ℂ) • (h.op*t o o)
  positive := by
    have he : h.op*t o o=t o o*h.op*star (t o o) := by
      rw [hu.adjoint,← (hc o o).eq,mul_assoc,(hu.diagonal_projection o).2]
    rw [he]
    exact (h.positive.conj_adjoint (t o o)).smul_of_nonneg (by simp [Complex.le_def])
  diagonal_summable := by
    simpa only [entry,smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      Complex.natCast_re,Complex.natCast_im,Complex.mul_re,zero_mul,sub_zero] using
      (hu.density_diagonal_summable h o).mul_left (Fintype.card ι:ℝ)
  trace_one := by
    simpa only [entry,smul_apply,lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,
      Complex.natCast_re,Complex.natCast_im,Complex.mul_re,zero_mul,sub_zero,tsum_mul_left] using
      hu.corner_mass h hP hc o

/-- The normalized corner is faithful on exactly its corner support. -/
theorem cornerDensity_support (hu : Units P t) (h : Density) (hP : SupportOf h P)
    (hc : ∀ i j,Commute h.op (t i j)) (o : ι) :
    SupportOf (hu.cornerDensity h hP hc o) (t o o) := by
  have hd : (Fintype.card ι:ℂ)≠0 := by
    have hn : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨o⟩
    exact_mod_cast Nat.ne_of_gt hn
  refine ⟨hu.diagonal_projection o,?_,?_⟩
  · change t o o*((Fintype.card ι:ℂ) • (h.op*t o o))=_
    rw [mul_smul_comm,← mul_assoc,← (hc o o).eq,mul_assoc,(hu.diagonal_projection o).2]
    rfl
  · intro v hv hz
    apply hP.2.2 v
    · have hh := congrArg (fun A : Op => A v) (hu.supported o o).1
      change P (t o o v)=t o o v at hh
      rwa [hv] at hh
    · change (Fintype.card ι:ℂ) • h.op (t o o v)=0 at hz
      rw [hv] at hz
      exact (smul_eq_zero.mp hz).resolve_left hd

/-- In the explicit coordinates, h=(I_d/d) tensor the normalized corner. -/
theorem density_coordinates (hu : Units P t) (h : Density) (hP : SupportOf h P)
    (hc : ∀ i j,Commute h.op (t i j)) (o i : ι) (v : H) :
    t o i (h.op v)=(Fintype.card ι:ℂ)⁻¹ •
      (hu.cornerDensity h hP hc o).op (t o i v) := by
  have hd : (Fintype.card ι:ℂ)≠0 := by
    have hn : 0<Fintype.card ι := Fintype.card_pos_iff.mpr ⟨o⟩
    exact_mod_cast Nat.ne_of_gt hn
  change t o i (h.op v)=(Fintype.card ι:ℂ)⁻¹ •
    ((Fintype.card ι:ℂ) • (h.op*(t o o)) (t o i v))
  rw [smul_smul,inv_mul_cancel₀ hd,one_smul]
  change (t o i*h.op) v=((h.op*t o o)*t o i) v
  rw [mul_assoc,hu.product,if_pos rfl]
  exact congrArg (fun A : Op => A v) (hc o i).eq.symm

#print axioms corner_trace_equal
#print axioms corner_mass
#print axioms cornerDensity_support
#print axioms density_coordinates
#print axioms sandwich_covariance
#print axioms sandwich_trace
#print axioms diagonal_projection
#print axioms diagonal_positive
#print axioms density_diagonal_summable

end Units
end Sigma2.MatrixSupportCoordinates