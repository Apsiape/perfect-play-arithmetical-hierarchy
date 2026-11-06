import Sigma2.BridgeTransfer
import Sigma2.MirrorCentralizer
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.SharpEvents
open Compiler TensorLifts PureSupport Preliminaries

/-- Exact matching of one outcome in two complete finite POVMs gives a sharp
compression on the actual support, without a projectivity hypothesis. -/
theorem single_matching_analysis {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (A B : Fin 6 → Op) (hA : ∀ a,Positive (A a)) (hB : ∀ b,Positive (B b))
    (sA : ∑ a,A a=1) (sB : ∑ b,B b=1) (a0 b0 : Fin 6)
    (hAB : ∀ b,b≠b0 → (inner ℂ S.vector ((left (A a0)*right (B b)) S.vector)).re=0)
    (hBA : ∀ a,a≠a0 → (inner ℂ S.vector ((left (A a)*right (B b0)) S.vector)).re=0) :
    left (A a0) S.vector=right (B b0) S.vector ∧
      A a0*P=P*A a0 ∧ Projection (P*A a0*P) := by
  have sL : (∑ a,left (A a))=1 := by rw [← left_sum,sA,left_one]
  have sR : (∑ b,right (B b))=1 := by rw [← right_sum,sB,right_one]
  have hLA : Positive (1-A a0) := by
    have hh := positive_sum_erase A hA a0
    rwa [sA] at hh
  have hRB : Positive (1-B b0) := by
    have hh := positive_sum_erase B hB b0
    rwa [sB] at hh
  have restR : 1-right (B b0)=∑ b ∈ Finset.univ.erase b0,right (B b) := by
    have hh := Finset.sum_erase_add Finset.univ (fun b => right (B b)) (Finset.mem_univ b0)
    rw [sR] at hh
    exact (eq_sub_iff_add_eq.mpr hh).symm
  have restL : 1-left (A a0)=∑ a ∈ Finset.univ.erase a0,left (A a) := by
    have hh := Finset.sum_erase_add Finset.univ (fun a => left (A a)) (Finset.mem_univ a0)
    rw [sL] at hh
    exact (eq_sub_iff_add_eq.mpr hh).symm
  have hzR : (left (A a0)*(1-right (B b0))) S.vector=0 := by
    rw [restR,Finset.mul_sum,sum_apply]
    apply Finset.sum_eq_zero
    intro b hb
    exact positive_apply_eq_zero _ (joint_positive _ _ (hA a0) (hB b)) _
      (hAB b (Finset.mem_erase.mp hb).1)
  have hzL : ((1-left (A a0))*right (B b0)) S.vector=0 := by
    rw [restL,Finset.sum_mul,sum_apply]
    apply Finset.sum_eq_zero
    intro a ha
    exact positive_apply_eq_zero _ (joint_positive _ _ (hA a) (hB b0)) _
      (hBA a (Finset.mem_erase.mp ha).1)
  have hleft : left (A a0) S.vector=left (A a0) (right (B b0) S.vector) := by
    change left (A a0) (S.vector-right (B b0) S.vector)=0 at hzR
    rw [map_sub] at hzR
    exact sub_eq_zero.mp hzR
  have hright : right (B b0) S.vector=left (A a0) (right (B b0) S.vector) := by
    change right (B b0) S.vector-left (A a0) (right (B b0) S.vector)=0 at hzL
    exact sub_eq_zero.mp hzL
  refine ⟨hleft.trans hright.symm,?_⟩
  apply matching_sharp S h hm P hP (A a0) (B b0) ⟨hA a0,hLA⟩ ⟨hB b0,hRB⟩
  have he : left (A a0)+right (B b0)-(2:ℂ) • (left (A a0)*right (B b0))=
      left (A a0)*(1-right (B b0))+(1-left (A a0))*right (B b0) := by
    rw [mul_sub,sub_mul,mul_one,one_mul]
    module
  rw [he,add_apply,hzR,hzL]
  simp

theorem single_matching_sharp {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (A B : Fin 6 → Op) (hA : ∀ a,Positive (A a)) (hB : ∀ b,Positive (B b))
    (sA : ∑ a,A a=1) (sB : ∑ b,B b=1) (a0 b0 : Fin 6)
    (hAB : ∀ b,b≠b0 → (inner ℂ S.vector ((left (A a0)*right (B b)) S.vector)).re=0)
    (hBA : ∀ a,a≠a0 → (inner ℂ S.vector ((left (A a)*right (B b0)) S.vector)).re=0) :
    A a0*P=P*A a0 ∧ Projection (P*A a0*P) := by
  exact (single_matching_analysis S h hm P hP A B hA hB sA sB a0 b0 hAB hBA).2

theorem single_matching_synchronized {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (A B : Fin 6 → Op) (hA : ∀ a,Positive (A a)) (hB : ∀ b,Positive (B b))
    (sA : ∑ a,A a=1) (sB : ∑ b,B b=1) (a0 b0 : Fin 6)
    (hAB : ∀ b,b≠b0 → (inner ℂ S.vector ((left (A a0)*right (B b)) S.vector)).re=0)
    (hBA : ∀ a,a≠a0 → (inner ℂ S.vector ((left (A a)*right (B b0)) S.vector)).re=0) :
    A a0*P=P*A a0 ∧ Projection (P*A a0*P) ∧ Centralizes h.op (A a0) := by
  have hh := single_matching_analysis S h hm P hP A B hA hB sA sB a0 b0 hAB hBA
  exact ⟨hh.2.1,hh.2.2,MirrorCentralizer.mirrors_centralize S h hm _ _ (hA a0) (hB b0) hh.1⟩

/-- First predicate-specific sharp extraction: the actual row-zero flag. -/
theorem conditional_flag_sharp {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    flagA (normalOfPure S) I*P=P*flagA (normalOfPure S) I ∧
      Projection (P*flagA (normalOfPure S) I*P) ∧
      Centralizes h.op (flagA (normalOfPure S) I) := by
  apply single_matching_synchronized S h hm P hP
    (fun a => S.measurements.alice (I.qA 0) (I.aA a))
    (fun b => S.measurements.bob (I.qB 0) (I.aB b))
    (fun a => S.measurements.alice_pos _ _) (fun b => S.measurements.bob_pos _ _)
    (hS.2.1 0) (hS.2.2 0) 0 0
  · intro b hb
    have hr : conditionalFmsRule 0 0 0 b.val=false := by
      fin_cases b <;> norm_num [conditionalFmsRule,fmsRule] at *
    have hh := hS.1 0 0 0 b hr
    rw [normalOfPure_probability] at hh
    change (inner ℂ S.vector ((S.measurements.left (I.qA 0) (I.aA 0)*
      S.measurements.right (I.qB 0) (I.aB b)) S.vector)).re=0 at hh
    rw [measurements_left,measurements_right] at hh
    exact hh
  · intro a ha
    have hr : conditionalFmsRule 0 0 a.val 0=false := by
      fin_cases a <;> norm_num [conditionalFmsRule,fmsRule] at *
    have hh := hS.1 0 0 a 0 hr
    rw [normalOfPure_probability] at hh
    change (inner ℂ S.vector ((S.measurements.left (I.qA 0) (I.aA a)*
      S.measurements.right (I.qB 0) (I.aB 0)) S.vector)).re=0 at hh
    rw [measurements_left,measurements_right] at hh
    exact hh


theorem conditional_retained_sharp {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x : Fin 2) (k : Fin 3) :
    let q : Fin 5 := ⟨x.val+3,by omega⟩
    let a : Fin 6 := ⟨k.val+2,by omega⟩
    let E := S.measurements.alice (I.qA q) (I.aA a)
    E*P=P*E ∧ Projection (P*E*P) ∧ Centralizes h.op E := by
  let q : Fin 5 := ⟨x.val+3,by omega⟩
  let a : Fin 6 := ⟨k.val+2,by omega⟩
  have hbnd : retained x.val k.val+1<6 := by
    dsimp [retained]
    split_ifs <;> omega
  let b : Fin 6 := ⟨retained x.val k.val+1,hbnd⟩
  have hAB (b' : Fin 6) (hb : b'≠b) :
      (inner ℂ S.vector ((left (S.measurements.alice (I.qA q) (I.aA a))*
        right (S.measurements.bob (I.qB 0) (I.aB b'))) S.vector)).re=0 := by
    have hr : conditionalFmsRule q.val 0 a.val b'.val=false := by
      dsimp [q,a,b] at *
      fin_cases x <;> fin_cases k <;> fin_cases b' <;>
        norm_num [conditionalFmsRule,fmsRule,retained] at *
    have hh := hS.1 q 0 a b' hr
    rw [normalOfPure_probability] at hh
    change (inner ℂ S.vector ((S.measurements.left (I.qA q) (I.aA a)*
      S.measurements.right (I.qB 0) (I.aB b')) S.vector)).re=0 at hh
    rw [measurements_left,measurements_right] at hh
    exact hh
  have hBA (a' : Fin 6) (ha : a'≠a) :
      (inner ℂ S.vector ((left (S.measurements.alice (I.qA q) (I.aA a'))*
        right (S.measurements.bob (I.qB 0) (I.aB b))) S.vector)).re=0 := by
    have hr : conditionalFmsRule q.val 0 a'.val b.val=false := by
      dsimp [q,a,b] at *
      fin_cases x <;> fin_cases k <;> fin_cases a' <;>
        norm_num [conditionalFmsRule,fmsRule,retained] at *
    have hh := hS.1 q 0 a' b hr
    rw [normalOfPure_probability] at hh
    change (inner ℂ S.vector ((S.measurements.left (I.qA q) (I.aA a')*
      S.measurements.right (I.qB 0) (I.aB b)) S.vector)).re=0 at hh
    rw [measurements_left,measurements_right] at hh
    exact hh
  have hh := single_matching_analysis S h hm P hP
    (fun a' => S.measurements.alice (I.qA q) (I.aA a'))
    (fun b' => S.measurements.bob (I.qB 0) (I.aB b'))
    (fun _ => S.measurements.alice_pos _ _) (fun _ => S.measurements.bob_pos _ _)
    (hS.2.1 q) (hS.2.2 0) a b hAB hBA
  exact ⟨hh.2.1,hh.2.2,MirrorCentralizer.mirrors_centralize S h hm _ _
    (S.measurements.alice_pos _ _) (S.measurements.bob_pos _ _) hh.1⟩

theorem conditional_magic_sharp {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (i : Fin 4) :
    magicA (normalOfPure S) I i*P=P*magicA (normalOfPure S) I i ∧
    Projection (P*magicA (normalOfPure S) I i*P) ∧
    Centralizes h.op (magicA (normalOfPure S) I i) := by
  fin_cases i
  · simpa [magicA,normalOfPure] using conditional_retained_sharp S I hS h hm P hP 1 0
  · simpa [magicA,normalOfPure] using conditional_retained_sharp S I hS h hm P hP 0 0
  · simpa [magicA,normalOfPure] using conditional_retained_sharp S I hS h hm P hP 0 1
  · simpa [magicA,normalOfPure] using conditional_retained_sharp S I hS h hm P hP 0 2

#print axioms conditional_flag_sharp
#print axioms conditional_magic_sharp
end Sigma2.SharpEvents
