import Sigma2.FourUnits
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.DiagonalIdentification
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits FourUnits

theorem retained_analysis {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (x : Fin 2) (k : Fin 3) :
    let q : Fin 5 := ⟨x.val+3,by omega⟩
    let a : Fin 6 := ⟨k.val+2,by omega⟩
    let E := S.measurements.alice (I.qA q) (I.aA a)
    left E S.vector=right (S.measurements.bob (I.qB 0)
      (I.aB ⟨retained x.val k.val+1,by dsimp [retained]; split_ifs <;> omega⟩)) S.vector ∧
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
  have hh := SharpEvents.single_matching_analysis S h hm P hP
    (fun a' => S.measurements.alice (I.qA q) (I.aA a'))
    (fun b' => S.measurements.bob (I.qB 0) (I.aB b'))
    (fun _ => S.measurements.alice_pos _ _) (fun _ => S.measurements.bob_pos _ _)
    (hS.2.1 q) (hS.2.2 0) a b hAB hBA
  exact ⟨hh.1,hh.2.1,hh.2.2,MirrorCentralizer.mirrors_centralize S h hm _ _
    (S.measurements.alice_pos _ _) (S.measurements.bob_pos _ _) hh.1⟩
theorem coarse_product {ι τ υ : Type} [Fintype ι] [DecidableEq ι] [DecidableEq τ] [DecidableEq υ]
    (B : ι → Op) (p : ι → τ) (q : ι → υ) (t : τ) (u : υ) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P) (hQ : Projection (coarse B p t)) :
    coarse B p t*coarse B q u=∑ a,if p a=t ∧ q a=u then B a else 0 := by
  conv_lhs => rhs; unfold coarse
  simp only [Finset.mul_sum,mul_ite,mul_zero,coarse_action B p t P hP hB hs hQ]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hp : p a=t <;> by_cases hq : q a=u <;> simp [hp,hq]

theorem active_coarse (B : Fin 6 → Op) (neg : Bool) (j : Fin 3) :
    active B=coarse B (cellClass neg j) 1+coarse B (cellClass neg j) 2 := by
  cases neg <;> fin_cases j <;> norm_num [active,coarse,cellClass,cellSign,Fin.sum_univ_succ] <;> abel

theorem projector_coarse (B : Fin 6 → Op) (neg : Bool) (j : Fin 3) (a : Fin 2) :
    projector (active B) (signed B (cellClass neg j)) a=
      coarse B (cellClass neg j) (if a=0 then 1 else 2) := by
  rw [active_coarse B neg j]
  fin_cases a <;> norm_num [projector,signed] <;> module

def answer (a b : Fin 2) : Fin 6 := ⟨2*a.val+b.val+1,by omega⟩

theorem joint_projector_outcome (B : Fin 6 → Op) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hp : ∀ j t,Projection (coarse B (cellClass false j) t)) (a b : Fin 2) :
    projector (active B) (signed B (cellClass false 0)) a*
      projector (active B) (signed B (cellClass false 1)) b=B (answer a b) := by
  rw [projector_coarse,projector_coarse,coarse_product B _ _ _ _ P hP hB hs (hp 0 _)]
  fin_cases a <;> fin_cases b <;>
    norm_num [answer,cellClass,cellSign,Fin.sum_univ_succ]

theorem magic_mirror {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (i : Fin 4) :
    left (magicA (normalOfPure S) I i) S.vector=
      right (S.measurements.bob (I.qB 0) (I.aB ⟨i.val+1,by omega⟩)) S.vector := by
  fin_cases i
  · simpa [magicA,normalOfPure,retained] using (retained_analysis S I hS h hm P hP 1 0).1
  · simpa [magicA,normalOfPure,retained] using (retained_analysis S I hS h hm P hP 0 0).1
  · simpa [magicA,normalOfPure,retained] using (retained_analysis S I hS h hm P hP 0 1).1
  · simpa [magicA,normalOfPure,retained] using (retained_analysis S I hS h hm P hP 0 2).1

theorem left_add (A B : Op) : left (A+B)=left A+left B := by
  ext v ⟨i,j⟩
  simp only [left_apply,add_apply,lp.coeFn_add,Pi.add_apply]

theorem right_add (A B : Op) : right (A+B)=right A+right B := by
  ext v ⟨i,j⟩
  simp only [right_apply,add_apply,lp.coeFn_add,Pi.add_apply]

theorem mirror_projector (v : AB) (e f Z W : Op)
    (he : left e v=right f v) (hz : left Z v=right W v) (a : Fin 2) :
    left (projector e Z a) v=right (projector f W a) v := by
  simp only [projector,left_smul,right_smul,left_add,right_add,smul_apply,add_apply,he,hz]

/-- The exact original magicA effects are the joint spectral projectors,
with bit order (i/2,i%2), without an independent relabelling. -/
theorem magic_diagonal {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) (i : Fin 4) :
    diagonal (rowActive S I P 0) (rowCell S I P 0 0) (rowCell S I P 1 0)
      (⟨i.val/2,by omega⟩,⟨i.val%2,by omega⟩)=P*magicA (normalOfPure S) I i*P := by
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  let B := compressed Q (colPOVM S I 0)
  have he := active_mirror S I hS h hB hm hmB P Q hP hQ 0 0
  have hc := cells_mirror S I hS h hB hm hmB P Q hP hQ
  have h0 := mirror_projector S.vector _ _ _ _ he (hc 0 0) (⟨i.val/2,by omega⟩ : Fin 2)
  have h1 := mirror_projector S.vector _ _ _ _ he (hc 1 0) (⟨i.val%2,by omega⟩ : Fin 2)
  have hcomm : Commute (projector (active B) (signed B (cellClass false 0)) ⟨i.val/2,by omega⟩)
      (projector (active B) (signed B (cellClass false 1)) ⟨i.val%2,by omega⟩) := by
    have hr := projector_coarse B false 0 (⟨i.val/2,by omega⟩ : Fin 2)
    have hs := projector_coarse B false 1 (⟨i.val%2,by omega⟩ : Fin 2)
    rw [hr,hs]
    have hpos := compressed_positive Q hQ.1 (colPOVM S I 0) (fun b => S.measurements.bob_pos _ _)
    have hsum := compressed_sum Q hQ.1 (colPOVM S I 0) (hS.2.2 0)
    have hsharpB (j : Fin 3) (t : Fin 4) : Projection (coarse B (cellClass false j) t) :=
      col_sharp S I hS hB hmB Q hQ j 0 t
    unfold Commute SemiconjBy
    rw [coarse_product B _ _ _ _ Q hQ.1 hpos hsum (hsharpB 0 _),
      coarse_product B _ _ _ _ Q hQ.1 hpos hsum (hsharpB 1 _)]
    simp only [and_comm]
  have hout := joint_projector_outcome B Q hQ.1
    (compressed_positive Q hQ.1 _ (fun b => S.measurements.bob_pos _ _))
    (compressed_sum Q hQ.1 _ (hS.2.2 0)) (fun j t => col_sharp S I hS hB hmB Q hQ j 0 t)
    (⟨i.val/2,by omega⟩ : Fin 2) (⟨i.val%2,by omega⟩ : Fin 2)
  have hbi : answer (⟨i.val/2,by omega⟩ : Fin 2) (⟨i.val%2,by omega⟩ : Fin 2)=⟨i.val+1,by omega⟩ := by
    apply Fin.ext
    dsimp [answer]
    omega
  have hmagi := compressed_mirror S.vector P Q _ _ (left_support S h hm P hP)
    (right_support S hB hmB Q hQ) (magic_mirror S I hS h hm P hP i)
  have hsig (j : Fin 3) : colCell S I Q j 0=signed B (cellClass false j) := rfl
  have heq : colActive S I Q 0=active B := rfl
  have hpp := mirror_mul S.vector _ _ _ _ h0 h1
  rw [hsig,hsig,heq] at hpp
  rw [hcomm.eq.symm,hout,hbi] at hpp
  apply local_eq S h hm P hP _ _
  · simp only [diagonal,projector,mul_assoc,mul_smul_comm,mul_add,add_mul,smul_mul_assoc,
      active_supported P hP.1,signed_supported P hP.1,rowActive,rowCell]
  · simp only [mul_assoc,hP.1.2]
  · exact hpp.trans hmagi.symm

#print axioms magic_diagonal
end Sigma2.DiagonalIdentification
