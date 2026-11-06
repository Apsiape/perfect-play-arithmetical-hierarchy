import Sigma2.RefinementCoarse
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RefinementLabel
open Compiler Preliminaries TensorLifts PureSupport CoarseCells MirrorAlgebra FiniteSpectral
  DiagonalIdentification RefinementCoarse

/-- Label matching identifies the original compressed label, proves it sharp,
and forces every new coarse outcome to commute with it. -/
theorem label_matching {s} {κ : Type} [Fintype κ] [DecidableEq κ]
    (S : PureStrategy s) (h : Density) (hm : MarginalA (normalOfPure S) h)
    (P : Op) (hP : SupportOf h P) (A : Fin 6 → Fin 2 → Op) (B : κ → Op)
    (hA : ∀ a z,Positive (A a z)) (hB : ∀ b,Positive (B b))
    (sA : (∑ a,∑ z,A a z)=1) (sB : ∑ b,B b=1) (b0 : κ) (L : Op)
    (hz : ∀ a z b,¬(z.val=1 ↔ b=b0) → (left (A a z)*right (B b)) S.vector=0)
    (hmirror : left L S.vector=right (B b0) S.vector) :
    (∑ a,P*A a 1*P)=P*L*P ∧ Projection (P*L*P) ∧
      ∀ a,(P*(∑ z,A a z)*P)*(P*L*P)=(P*L*P)*(P*(∑ z,A a z)*P) := by
  let Af : Fin 6 × Fin 2 → Op := fun az => A az.1 az.2
  let p : Fin 6 × Fin 2 → Fin 2 := fun az => az.2
  let q : κ → Fin 2 := fun b => if b=b0 then 1 else 0
  have hAf : ∀ az,Positive (Af az) := fun az => hA az.1 az.2
  have hsAf : (∑ az,Af az)=1 := by simpa only [Af,Fintype.sum_prod_type] using sA
  have hzero (az : Fin 6 × Fin 2) (b : κ) (hne : p az≠q b) :
      (inner ℂ S.vector ((left (Af az)*right (B b)) S.vector)).re=0 := by
    have hr : ¬(az.2.val=1 ↔ b=b0) := by
      intro he
      apply hne
      dsimp [p,q]
      rcases az with ⟨a,z⟩
      fin_cases z <;> by_cases hb : b=b0 <;> simp_all
    rw [hz az.1 az.2 b hr]
    simp
  have hh := coarse_analysis S h hm P hP Af B hAf hB hsAf sB p q hzero 1
  have hAc : coarse Af p 1=∑ a,A a 1 := by
    simp [coarse,Af,p,Fintype.sum_prod_type,Fin.sum_univ_two]
  have hBc : coarse B q 1=B b0 := by
    simp [coarse,q]
  rw [hAc,hBc] at hh
  have hv := hh.1.trans hmirror.symm
  have hcol : P*(∑ a,A a 1)*P=P*L*P := by
    apply local_eq S h hm P hP _ _
      (by simp only [mul_assoc,hP.1.2]) (by simp only [mul_assoc,hP.1.2])
    simp only [left_mul]
    change left P (left (∑ a,A a 1) (left P S.vector))=left P (left L (left P S.vector))
    rw [left_support S h hm P hP,hv]
  have hp : Projection (P*L*P) := hcol ▸ hh.2.2.1
  have hc : (∑ a,P*A a 1*P)=P*L*P := by
    rw [← Finset.sum_mul,← Finset.mul_sum]
    exact hcol
  refine ⟨hc,hp,?_⟩
  have hQ : ∀ a z,Positive (P*A a z*P) := by
    intro a z
    exact compressed_positive P hP.1 (A a) (hA a) z
  have htotal : (∑ a,∑ z,P*A a z*P)=P := by
    simp only [← Finset.sum_mul,← Finset.mul_sum,sA,mul_one,hP.1.2]
  have heP : P*(P*L*P)=P*L*P := by simp only [← mul_assoc,hP.1.2]
  have hPe : (P*L*P)*P=P*L*P := by simp only [mul_assoc,hP.1.2]
  have hj := RefinementAlgebra.fine_commutes P (P*L*P) hP.1 hp heP hPe
    (fun a z => P*A a z*P) hQ htotal hc
  intro a
  simpa only [← Finset.sum_mul,← Finset.mul_sum] using hj a

theorem alice_label {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    ∀ a,(P*aliceNew S F a*P)*(P*S.measurements.alice F.labelQA F.labelA*P)=
      (P*S.measurements.alice F.labelQA F.labelA*P)*(P*aliceNew S F a*P) := by
  rcases hF with ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩
  apply (label_matching S h hm P hP
    (fun a z => S.measurements.alice F.newA (F.answerA a z))
    (S.measurements.bob F.labelQB)
    (fun a z => S.measurements.alice_pos _ _) (S.measurements.bob_pos F.labelQB)
    sa (S.measurements.bob_sum F.labelQB) F.labelB
    (S.measurements.alice F.labelQA F.labelA) ?_ ?_).2.2
  · intro a z b hr
    exact event_zero S _ _ _ _ (hza a z b hr)
  · have hh := hlabel 0 (by norm_num [normalOfPure])
    rw [measurements_left,measurements_right] at hh
    exact hh

theorem bob_label {s} (S : PureStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) (hF : RefinementPerfect (normalOfPure S) I F)
    (h : Density) (hm : MarginalB (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    ∀ b,(P*bobNew S F b*P)*(P*S.measurements.bob F.labelQB F.labelB*P)=
      (P*S.measurements.bob F.labelQB F.labelB*P)*(P*bobNew S F b*P) := by
  rcases hF with ⟨hc,sa,sb,ha,hb,hza,hzb,hlabel⟩
  apply (label_matching (PureTransfer.flipPure S) h hm P hP
    (fun b z => S.measurements.bob F.newB (F.answerB b z))
    (S.measurements.alice F.labelQA)
    (fun b z => S.measurements.bob_pos _ _) (S.measurements.alice_pos F.labelQA)
    sb (S.measurements.alice_sum F.labelQA) F.labelA
    (S.measurements.bob F.labelQB F.labelB) ?_ ?_).2.2
  · intro b z a hr
    apply event_zero (PureTransfer.flipPure S) F.newB F.labelQA (F.answerB b z) a
    have hh := hzb a b z hr
    rw [normalOfPure_probability] at hh
    exact (normalOfPure_probability (PureTransfer.flipPure S) F.newB F.labelQA (F.answerB b z) a).trans
      ((PureTransfer.flipPure_probability S F.labelQA F.newB a (F.answerB b z)).trans hh)
  · have hh := hlabel 0 (by norm_num [normalOfPure])
    rw [measurements_left,measurements_right] at hh
    have hs := congrArg TensorLifts.swap hh
    rw [PureTransfer.swap_left,PureTransfer.swap_right] at hs
    exact hs.symm

#print axioms label_matching
#print axioms alice_label
#print axioms bob_label
end Sigma2.RefinementLabel

