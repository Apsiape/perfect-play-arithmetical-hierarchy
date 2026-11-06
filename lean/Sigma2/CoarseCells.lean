import Sigma2.SharpEvents
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CoarseCells
open Compiler TensorLifts PureSupport Preliminaries Coefficients

theorem finite_matching_analysis {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (A : ι → Op) (B : κ → Op) (hA : ∀ a,Positive (A a)) (hB : ∀ b,Positive (B b))
    (sA : ∑ a,A a=1) (sB : ∑ b,B b=1) (a0 : ι) (b0 : κ)
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
/-- Coarse effects retain the actual finite measurement. -/
def coarse {ι τ : Type} [Fintype ι] [DecidableEq τ]
    (A : ι → Op) (p : ι → τ) (t : τ) : Op :=
  ∑ a, if p a=t then A a else 0

theorem coarse_positive {ι τ : Type} [Fintype ι] [DecidableEq τ]
    (A : ι → Op) (p : ι → τ) (t : τ) (hA : ∀ a,Positive (A a)) :
    Positive (coarse A p t) := by
  apply ContinuousLinearMap.isPositive_sum
  intro a _
  split_ifs
  · exact hA a
  · exact ContinuousLinearMap.isPositive_zero

theorem coarse_sum {ι τ : Type} [Fintype ι] [Fintype τ] [DecidableEq τ]
    (A : ι → Op) (p : ι → τ) : ∑ t,coarse A p t=∑ a,A a := by
  unfold coarse
  rw [Finset.sum_comm]
  congr 1
  funext a
  simp

@[simp] theorem left_zero : left 0=0 := by ext v ⟨i,j⟩; simp [left_apply]
@[simp] theorem right_zero : right 0=0 := by ext v ⟨i,j⟩; simp [right_apply]

/-- A finite forbidden-event partition synchronizes every coarse effect. -/
theorem coarse_analysis {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]
    [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] {s}
    (S : PureStrategy s) (h : Density) (hm : MarginalA (normalOfPure S) h)
    (P : Op) (hP : SupportOf h P)
    (A : ι → Op) (B : κ → Op) (hA : ∀ a,Positive (A a)) (hB : ∀ b,Positive (B b))
    (sA : ∑ a,A a=1) (sB : ∑ b,B b=1) (p : ι → τ) (q : κ → τ)
    (hz : ∀ a b,p a≠q b →
      (inner ℂ S.vector ((left (A a)*right (B b)) S.vector)).re=0) (t : τ) :
    left (coarse A p t) S.vector=right (coarse B q t) S.vector ∧
    coarse A p t*P=P*coarse A p t ∧ Projection (P*coarse A p t*P) ∧
      Centralizes h.op (coarse A p t) := by
  have hzero (u v : τ) (hne : u≠v) :
      (inner ℂ S.vector ((left (coarse A p u)*right (coarse B q v)) S.vector)).re=0 := by
    unfold coarse
    rw [left_sum,right_sum,Finset.sum_mul]
    simp only [Finset.mul_sum,sum_apply,inner_sum,complex_re_sum]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    by_cases ha : p a=u <;> by_cases hb : q b=v
    · simp only [ha,hb,ite_true]
      exact hz a b (by intro he; exact hne (ha.symm.trans (he.trans hb)))
    all_goals simp [ha,hb]
  have hh := finite_matching_analysis S h hm P hP (coarse A p) (coarse B q)
    (fun u => coarse_positive A p u hA) (fun v => coarse_positive B q v hB)
    ((coarse_sum A p).trans sA) ((coarse_sum B q).trans sB) t t
    (fun v hv => hzero t v hv.symm) (fun u hu => hzero u t hu)
  exact ⟨hh.1,hh.2.1,hh.2.2,MirrorCentralizer.mirrors_centralize S h hm _ _
    (coarse_positive A p t hA) (coarse_positive B q t hB) hh.1⟩

/-- Four magic outcomes, the common flag, and the inactive outcome remain distinct. -/
def cellClass (neg : Bool) (j : Fin 3) (a : Fin 6) : Fin 4 :=
  if a=0 then 0 else if a=5 then 3 else if cellSign neg (a.val-1) j.val then 2 else 1

def rowEffect {s} (S : PureStrategy s) (I : FMSInstance s) (x y : Fin 3) (t : Fin 4) : Op :=
  coarse (fun a => S.measurements.alice (I.qA ⟨x.val,by omega⟩) (I.aA a))
    (cellClass false y) t

def colEffect {s} (S : PureStrategy s) (I : FMSInstance s) (x y : Fin 3) (t : Fin 4) : Op :=
  coarse (fun b => S.measurements.bob (I.qB ⟨y.val,by omega⟩) (I.aB b))
    (cellClass (decide (y.val=2)) x) t

theorem cellClass_forbidden (x y : Fin 3) (a b : Fin 6)
    (hne : cellClass false y a≠cellClass (decide (y.val=2)) x b) :
    conditionalFmsRule x.val y.val a.val b.val=false := by
  fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;>
    norm_num [cellClass,cellSign,conditionalFmsRule,fmsRule] at *

/-- The nine actual coarse cells match, are sharp on the actual support,
reduce that support, and centralize the original marginal. -/
theorem conditional_cells {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x y : Fin 3) (t : Fin 4) :
    left (rowEffect S I x y t) S.vector=right (colEffect S I x y t) S.vector ∧
    rowEffect S I x y t*P=P*rowEffect S I x y t ∧
    Projection (P*rowEffect S I x y t*P) ∧ Centralizes h.op (rowEffect S I x y t) := by
  apply coarse_analysis S h hm P hP
    (fun a => S.measurements.alice (I.qA ⟨x.val,by omega⟩) (I.aA a))
    (fun b => S.measurements.bob (I.qB ⟨y.val,by omega⟩) (I.aB b))
    (fun a => S.measurements.alice_pos _ _) (fun b => S.measurements.bob_pos _ _)
    (hS.2.1 ⟨x.val,by omega⟩) (hS.2.2 ⟨y.val,by omega⟩)
    (cellClass false y) (cellClass (decide (y.val=2)) x) ?_ t
  intro a b hab
  have hh := hS.1 ⟨x.val,by omega⟩ ⟨y.val,by omega⟩ a b (cellClass_forbidden x y a b hab)
  rw [normalOfPure_probability] at hh
  change (inner ℂ S.vector ((S.measurements.left _ _*S.measurements.right _ _) S.vector)).re=0 at hh
  rw [measurements_left,measurements_right] at hh
  exact hh

#print axioms conditional_cells
end Sigma2.CoarseCells
