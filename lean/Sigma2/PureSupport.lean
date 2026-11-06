import Sigma2.Preliminaries
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.PureSupport
open Coefficients TensorLifts Preliminaries

theorem op_ext (A B : Op) (h : ∀ i j,entry A i j=entry B i j) : A=B := by
  apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞)≠⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro c
  change A (lp.single 2 j c)=B (lp.single 2 j c)
  have he : (lp.single 2 j c : H)=c • basis j := by
    simp only [basis,← lp.single_smul,smul_eq_mul,mul_one]
  rw [he,map_smul,map_smul]
  congr 1
  ext i
  exact h i j

theorem marginalA_covariance {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) :
    h.op=covariance (fun j => column S.vector j) := by
  apply op_ext
  intro i j
  rw [show entry (covariance (fun j => column S.vector j)) i j=
      ∑' b,S.vector (i,b)*star (S.vector (j,b)) from
    covariance_entry _ (column_mass S.vector).1 i j]
  have hh := hm i j
  have he (k : ℕ) : ((if k=0 then 1 else 0 : ℝ):ℂ)=if k=0 then 1 else 0 := by
    split_ifs <;> rfl
  simpa [normalOfPure,he,ite_mul] using hh

/-- A positive local operator with zero pure expectation kills each actual column. -/
theorem zero_columns (B : Op) (hB : Positive B) (v : AB)
    (hz : (inner ℂ v (left B v)).re=0) : ∀ j,B (column v j)=0 := by
  have hh := positive_apply_eq_zero (left B) (left_positive B hB) v hz
  intro j
  have hc := congrArg (fun w : AB => column w j) hh
  have h0 : column (0:AB) j=0 := by ext i; rfl
  simpa only [column_left,h0] using hc

/-- Faithfulness on the actual support turns column-wise vanishing into
vanishing of the original compressed local operator. -/
theorem zero_on_support {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (B : Op) (hB : Positive B)
    (hz : (inner ℂ S.vector (left B S.vector)).re=0) : B*P=0 ∧ P*B=0 := by
  have hcol := zero_columns B hB S.vector hz
  have hc := marginalA_covariance S h hm
  have hPB : P*B=0 := by
    apply ContinuousLinearMap.ext
    intro v
    change P (B v)=0
    apply hP.2.2 (P (B v))
    · exact congrArg (fun L : Op => L (B v)) hP.1.2
    · have hright : h.op*P=h.op := by
        have hh := congrArg (fun L : Op => star L) hP.2.1
        simpa only [star_mul,hP.1.1,h.positive.isSelfAdjoint.star_eq] using hh
      have he : h.op (P (B v))=h.op (B v) :=
        congrArg (fun L : Op => L (B v)) hright
      rw [he,hc]
      apply (covariance_kernel _ (column_mass S.vector).1 (B v)).mpr
      intro j
      calc
        _ = inner ℂ v (B (column S.vector j)) := hB.isSymmetric v _
        _ = 0 := by rw [hcol j,inner_zero_right]
  refine ⟨?_,hPB⟩
  have hh := congrArg (fun L : Op => star L) hPB
  simp only [star_mul,hP.1.1,hB.isSelfAdjoint.star_eq] at hh
  exact hh.trans (star_zero Op)


/-- Column-wise vanishing descends to the actual support for any bounded map. -/
theorem columns_zero_support {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (C : Op) (hC : ∀ j,C (column S.vector j)=0) : C*P=0 := by
  have hc := marginalA_covariance S h hm
  have hright : h.op*P=h.op := by
    have hh := congrArg (fun L : Op => star L) hP.2.1
    simpa only [star_mul,hP.1.1,h.positive.isSelfAdjoint.star_eq] using hh
  have hPC : P*star C=0 := by
    apply ContinuousLinearMap.ext
    intro v
    change P (star C v)=0
    apply hP.2.2 (P (star C v))
    · exact congrArg (fun L : Op => L (star C v)) hP.1.2
    · have he := congrArg (fun L : Op => L (star C v)) hright
      change h.op (P (star C v))=h.op (star C v) at he
      rw [he,hc]
      apply (covariance_kernel _ (column_mass S.vector).1 (star C v)).mpr
      intro j
      calc
        _ = inner ℂ v (C (column S.vector j)) := C.adjoint_inner_left _ _
        _ = 0 := by rw [hC j,inner_zero_right]
  have hh := congrArg (fun L : Op => star L) hPC
  simp only [star_mul,star_star,hP.1.1] at hh
  exact hh.trans (star_zero Op)

theorem columns_supported {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    ∀ j,P (column S.vector j)=column S.vector j := by
  have hc := marginalA_covariance S h hm
  have hright : h.op*P=h.op := by
    have hh := congrArg (fun L : Op => star L) hP.2.1
    simpa only [star_mul,hP.1.1,h.positive.isSelfAdjoint.star_eq] using hh
  have hk : h.op*(1-P)=0 := by rw [mul_sub,mul_one,hright,sub_self]
  have hsP : IsSelfAdjoint P := hP.1.1
  have hsd : IsSelfAdjoint ((1:Op)-P) :=
    (star_sub (1:Op) P).trans (congrArg₂ (fun X Y : Op => X-Y) (star_one Op) hsP)
  have hs : ((1:Op)-P).IsSymmetric :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsd
  intro j
  have hz : (1-P) (column S.vector j)=0 := by
    apply ext_inner_left ℂ
    intro v
    rw [inner_zero_right]
    have hh := congrArg (fun L : Op => L v) hk
    change h.op ((1-P) v)=0 at hh
    rw [hc] at hh
    have hh' := (covariance_kernel _ (column_mass S.vector).1 ((1-P) v)).mp hh j
    exact (hs v (column S.vector j)).symm.trans hh'
  change column S.vector j-P (column S.vector j)=0 at hz
  exact (sub_eq_zero.mp hz).symm

theorem matching_commutes_support {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (E F : Op) (hE : Positive E)
    (hmatch : left E S.vector=right F S.vector) : E*P=P*E := by
  have hzero : left (1-P) S.vector=0 := by
    ext ⟨i,j⟩
    change ((1-P) (column S.vector j)) i=0
    have hh := columns_supported S h hm P hP j
    change (column S.vector j-P (column S.vector j)) i=0
    rw [hh,sub_self]
    rfl
  have hl : left ((1-P)*E) S.vector=0 := by
    rw [left_mul]
    change left (1-P) (left E S.vector)=0
    rw [hmatch]
    have hc := congrArg (fun L : BipOp => L S.vector) (commute (1-P) F)
    change left (1-P) (right F S.vector)=right F (left (1-P) S.vector) at hc
    rw [hc,hzero,map_zero]
  have hcol j : ((1-P)*E) (column S.vector j)=0 := by
    have hh := congrArg (fun v : AB => column v j) hl
    have h0 : column (0:AB) j=0 := by ext i; rfl
    simpa only [column_left,h0] using hh
  have hCP := columns_zero_support S h hm P hP ((1-P)*E) hcol
  have hEP : E*P=P*E*P := by
    rw [sub_mul,one_mul,sub_mul] at hCP
    exact sub_eq_zero.mp hCP
  have hPE : P*E=P*E*P := by
    have hh := congrArg (fun L : Op => star L) hEP
    simpa only [star_mul,hP.1.1,hE.isSelfAdjoint.star_eq,mul_assoc] using hh
  exact hEP.trans hPE.symm

theorem local_defect_positive (E : Op) (hE : Positive E) (hE' : Positive (1-E)) :
    Positive (E-E*E) := by
  have h0 : 0 ≤ E := ContinuousLinearMap.nonneg_iff_isPositive.mpr hE
  have h1 : E ≤ 1 := hE'
  exact CStarAlgebra.mul_self_le_of_nonneg_of_norm_le_one h0
    ((CStarAlgebra.norm_le_one_iff_of_nonneg E h0).mpr h1)

theorem left_sub (A B : Op) : left (A-B)=left A-left B := by
  ext v ⟨i,j⟩
  simp only [left_apply,sub_apply,lp.coeFn_sub,Pi.sub_apply]

/-- Sharpness is obtained on the actual marginal support from a pure zero-mismatch
identity. The full-space effects need not have been sharp beforehand. -/
theorem matching_sharp {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (E F : Op) (hE : PositiveContraction E) (hF : PositiveContraction F)
    (hz : (inner ℂ S.vector ((left E+right F-(2:ℂ) • (left E*right F)) S.vector)).re=0) :
    E*P=P*E ∧ Projection (P*E*P) := by
  have hEc : left (1-E)=1-left E := by rw [left_sub,left_one]
  have hFc : right (1-F)=1-right F := by
    ext v ⟨i,j⟩
    simp only [right_apply,sub_apply,lp.coeFn_sub,Pi.sub_apply,one_apply_eq_self]
    rfl
  have hmismatch := matching_on_vector (left E) (right F) S.vector
    (left_positive E hE.1) (hEc ▸ left_positive (1-E) hE.2)
    (right_positive F hF.1) (hFc ▸ right_positive (1-F) hF.2) (commute E F) hz
  have hcomm := matching_commutes_support S h hm P hP E F hE.1 hmismatch.1
  have hd : left (E-E*E) S.vector=0 := by
    rw [left_sub,left_mul]
    exact hmismatch.2.1
  have hdexp : (inner ℂ S.vector (left (E-E*E) S.vector)).re=0 := by rw [hd]; simp
  have hdP := (zero_on_support S h hm P hP (E-E*E)
    (local_defect_positive E hE.1 hE.2) hdexp).1
  have heq : (E*E)*P=E*P := by
    rw [sub_mul] at hdP
    exact (sub_eq_zero.mp hdP).symm
  have hPEP : P*E*P=E*P := by rw [← hcomm,mul_assoc,hP.1.2]
  refine ⟨hcomm,?_,?_⟩
  · rw [star_mul,star_mul,hP.1.1,hE.1.isSelfAdjoint.star_eq]
    exact (mul_assoc P E P).symm
  · rw [hPEP]
    calc
      (E*P)*(E*P)=E*(P*E)*P := by noncomm_ring
      _ = E*(E*P)*P := by rw [← hcomm]
      _ = (E*E)*(P*P) := by noncomm_ring
      _ = (E*E)*P := by rw [hP.1.2]
      _ = E*P := heq

#print axioms zero_on_support
#print axioms matching_sharp
end Sigma2.PureSupport
