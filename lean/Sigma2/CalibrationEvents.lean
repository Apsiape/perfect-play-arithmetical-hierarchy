import Sigma2.BridgeMatrixUnits
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.CalibrationEvents
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral MagicCells MagicRelations MirrorAlgebra DiagonalIdentification

def signQuestion (x : Fin 2) : Fin 5 := ⟨x.val+3,by omega⟩

def signA {s} (S : PureStrategy s) (I : FMSInstance s) (x : Fin 2) : Op :=
  S.measurements.alice (I.qA (signQuestion x)) (I.aA 0)-
    S.measurements.alice (I.qA (signQuestion x)) (I.aA 1)

def sumA {s} (S : PureStrategy s) (I : FMSInstance s) (x : Fin 2) : Op :=
  S.measurements.alice (I.qA (signQuestion x)) (I.aA 0)+
    S.measurements.alice (I.qA (signQuestion x)) (I.aA 1)

def signB {s} (S : PureStrategy s) (I : FMSInstance s) (y : Fin 2) : Op :=
  S.measurements.bob (I.qB (signQuestion y)) (I.aB 0)-
    S.measurements.bob (I.qB (signQuestion y)) (I.aB 1)

def sumB {s} (S : PureStrategy s) (I : FMSInstance s) (y : Fin 2) : Op :=
  S.measurements.bob (I.qB (signQuestion y)) (I.aB 0)+
    S.measurements.bob (I.qB (signQuestion y)) (I.aB 1)

def signClassA (a : Fin 6) : Fin 6 :=
  if a.val<2 then 0 else if a=5 then 5 else ⟨a.val-1,by omega⟩

def signClassB (x : Fin 2) (b : Fin 6) : Fin 6 :=
  if b=0 ∨ b.val=x.val+1 then 0 else if b=5 then 5
  else ⟨if b.val≤x.val then b.val else b.val-1,by split_ifs <;> omega⟩

theorem signClass_forbidden (x : Fin 2) (a b : Fin 6)
    (hab : signClassA a≠signClassB x b) :
    conditionalFmsRule (signQuestion x).val 0 a.val b.val=false := by
  fin_cases x <;> fin_cases a <;> fin_cases b <;>
    norm_num [signClassA,signClassB,signQuestion,conditionalFmsRule,fmsRule,retained] at *

/-- The actual sign sector is sharp on the original support and has its
exact flag-plus-selected-outcome mirror; individual signs are not assumed sharp. -/
theorem sign_sector {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (x : Fin 2) :
    left (sumA S I x) S.vector=
      right (S.measurements.bob (I.qB 0) (I.aB 0)+
        S.measurements.bob (I.qB 0) (I.aB ⟨x.val+1,by omega⟩)) S.vector ∧
    sumA S I x*P=P*sumA S I x ∧ Projection (P*sumA S I x*P) ∧ Centralizes h.op (sumA S I x) := by
  have hz (a b : Fin 6) (hab : signClassA a≠signClassB x b) :
      (inner ℂ S.vector ((left (S.measurements.alice (I.qA (signQuestion x)) (I.aA a))*
        right (S.measurements.bob (I.qB 0) (I.aB b))) S.vector)).re=0 := by
    have hh := hS.1 (signQuestion x) 0 a b (signClass_forbidden x a b hab)
    rw [normalOfPure_probability] at hh
    change (inner ℂ S.vector ((S.measurements.left _ _*S.measurements.right _ _) S.vector)).re=0 at hh
    rw [measurements_left,measurements_right] at hh
    exact hh
  have hh := coarse_analysis S h hm P hP
    (fun a => S.measurements.alice (I.qA (signQuestion x)) (I.aA a))
    (fun b => S.measurements.bob (I.qB 0) (I.aB b))
    (fun a => S.measurements.alice_pos _ _) (fun b => S.measurements.bob_pos _ _)
    (hS.2.1 (signQuestion x)) (hS.2.2 0) signClassA (signClassB x) hz 0
  fin_cases x <;> simpa [coarse,signClassA,signClassB,sumA,signQuestion,Fin.sum_univ_succ] using hh

theorem forbidden_sign_zero {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (x y a b : Fin 2)
    (hab : (a.val+b.val)%2≠(x.val*y.val)%2) :
    (left (S.measurements.alice (I.qA (signQuestion x)) (I.aA ⟨a.val,by omega⟩))*
      right (S.measurements.bob (I.qB (signQuestion y)) (I.aB ⟨b.val,by omega⟩))) S.vector=0 := by
  have hr : conditionalFmsRule (signQuestion x).val (signQuestion y).val a.val b.val=false := by
    fin_cases x <;> fin_cases y <;> fin_cases a <;> fin_cases b <;>
      norm_num [signQuestion,conditionalFmsRule,fmsRule] at *
  have hh := hS.1 (signQuestion x) (signQuestion y) ⟨a.val,by omega⟩ ⟨b.val,by omega⟩ hr
  rw [normalOfPure_probability] at hh
  change (inner ℂ S.vector ((S.measurements.left _ _*S.measurements.right _ _) S.vector)).re=0 at hh
  rw [measurements_left,measurements_right] at hh
  exact positive_apply_eq_zero _ (joint_positive _ _ (S.measurements.alice_pos _ _)
    (S.measurements.bob_pos _ _)) _ hh

theorem parity_even (v : AB) (A0 A1 B0 B1 : Op)
    (h01 : (left A0*right B1) v=0) (h10 : (left A1*right B0) v=0) :
    (left (A0-A1)*right (B0+B1)) v=(left (A0+A1)*right (B0-B1)) v := by
  have h01' : left A0 (right B1 v)=0 := h01
  have h10' : left A1 (right B0 v)=0 := h10
  simp only [left_sub,right_add,left_add,right_sub]
  change (left A0-left A1) (right B0 v+right B1 v)=
    (left A0+left A1) (right B0 v-right B1 v)
  simp only [sub_apply,add_apply,map_add,map_sub,h01',h10']
  abel

theorem parity_odd (v : AB) (A0 A1 B0 B1 : Op)
    (h00 : (left A0*right B0) v=0) (h11 : (left A1*right B1) v=0) :
    (left (A0-A1)*right (B0+B1)) v= -((left (A0+A1)*right (B0-B1)) v) := by
  have h00' : left A0 (right B0 v)=0 := h00
  have h11' : left A1 (right B1 v)=0 := h11
  simp only [left_sub,right_add,left_add,right_sub]
  change (left A0-left A1) (right B0 v+right B1 v)=
    -((left A0+left A1) (right B0 v-right B1 v))
  simp only [sub_apply,add_apply,map_add,map_sub,h00',h11']
  abel

/-- The four exact sign-sector vector identities forced by conditional perfection. -/
theorem conditional_sign_parity {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (x y : Fin 2) :
    (left (signA S I x)*right (sumB S I y)) S.vector=
      (if x.val*y.val%2=0 then (1:ℂ) else -1) •
        ((left (sumA S I x)*right (signB S I y)) S.vector) := by
  by_cases he : x.val*y.val%2=0
  · rw [if_pos he,one_smul]
    apply parity_even
    · exact forbidden_sign_zero S I hS x y 0 1 (by norm_num; omega)
    · exact forbidden_sign_zero S I hS x y 1 0 (by norm_num; omega)
  · rw [if_neg he]
    have hh : (left (signA S I x)*right (sumB S I y)) S.vector=
        -((left (sumA S I x)*right (signB S I y)) S.vector) := by
      apply parity_odd
      · exact forbidden_sign_zero S I hS x y 0 0 (by norm_num; omega)
      · exact forbidden_sign_zero S I hS x y 1 1 (by norm_num; omega)
    rw [hh]
    module

theorem flag_mirror {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    left (flagA (normalOfPure S) I) S.vector=
      right (S.measurements.bob (I.qB 0) (I.aB 0)) S.vector := by
  have hh := (conditional_cells S I hS h hm P hP 0 0 0).1
  simpa [rowEffect,colEffect,coarse,cellClass,cellSign,Fin.sum_univ_succ,flagA,normalOfPure] using hh

/-- The actual sign sums are exactly f+m0 and f+m1 after support compression. -/
theorem sign_sector_identification {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (x : Fin 2) :
    P*sumA S I x*P=P*flagA (normalOfPure S) I*P+
      P*magicA (normalOfPure S) I ⟨x.val,by omega⟩*P := by
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  have hh := (sign_sector S I hS h hm P hP x).1
  have hmagic := magic_mirror S I hS h hm P hP (⟨x.val,by omega⟩ : Fin 4)
  have hflag := flag_mirror S I hS h hm P hP
  have hfm : left (flagA (normalOfPure S) I+magicA (normalOfPure S) I ⟨x.val,by omega⟩) S.vector=
      right (S.measurements.bob (I.qB 0) (I.aB 0)+
        S.measurements.bob (I.qB 0) (I.aB ⟨x.val+1,by omega⟩)) S.vector := by
    simp only [left_add,right_add,add_apply,hflag,hmagic]
  have hs1 := compressed_mirror S.vector P Q _ _ (left_support S h hm P hP)
    (right_support S hB hmB Q hQ) hh
  have hs2 := compressed_mirror S.vector P Q _ _ (left_support S h hm P hP)
    (right_support S hB hmB Q hQ) hfm
  have he := local_eq S h hm P hP _ _
    (show (P*sumA S I x*P)*P=P*sumA S I x*P by simp only [mul_assoc,hP.1.2])
    (show (P*(flagA (normalOfPure S) I+magicA (normalOfPure S) I ⟨x.val,by omega⟩)*P)*P=
      P*(flagA (normalOfPure S) I+magicA (normalOfPure S) I ⟨x.val,by omega⟩)*P by
        simp only [mul_assoc,hP.1.2]) (hs1.trans hs2.symm)
  simpa only [mul_add,add_mul] using he

#print axioms sign_sector_identification
#print axioms sign_sector
#print axioms conditional_sign_parity
end Sigma2.CalibrationEvents
