import Sigma2.CompilerApproxDictionary

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxLabels
open Compiler CompilerScaffold CompilerHonestDictionary CompilerFiniteRegister
  CompilerHonestLift CompilerHonestLabels CompilerHonestSyntax FiniteAncilla
  CompilerApproxDictionary

 theorem corner_diagonal (d : ℕ) [NeZero d] (a : Fin d) (A : Fin d → Op) :
    CompilerFiniteRegister.corner d a*diagonal d A=lift d a a (A a) := by
  rw [CompilerFiniteRegister.corner,diagonal_mul]
  unfold diagonal lift
  congr 1
  ext i j
  by_cases hi : i=a <;> by_cases hj : j=a <;> by_cases hij : i=j <;>
    simp_all [CompilerApproxBlocks.singleBlocks]

 theorem decode_copy (a : Fin 17) (U V : Op) (t : LabelType) :
    decodeEncoding (CompilerFiniteRegister.corner 17 a) (copy 17 a U) (copy 17 a V) t=
      lift 17 a a (decodeEncoding 1 U V t) := by
  have hs : star (copy 17 a U)=diagonal 17 (fun i => if i=a then star U else 1) := by
    rw [copy,diagonal_star]
    congr 1
    funext i
    split_ifs <;> simp
  cases t <;> simp only [decodeEncoding,one_mul]
  · exact corner_copy 17 a U
  · simp only [mul_smul_comm,mul_add,mul_one]
    rw [corner_copy]
    simp only [corner_lift,lift_smul,lift_add]
  · rw [hs]
    simp only [mul_smul_comm,mul_add,mul_one]
    rw [corner_copy,corner_diagonal,if_pos rfl]
    simp only [corner_lift,lift_smul,lift_add]
  · simp only [mul_smul_comm,mul_add,corner_copy,lift_smul,lift_add]

 theorem second_lt (P : Presentation) (i : Fin P.types.length) (ht : P.types[i.val]=.contraction) :
    encodingOffset P i.val+1<encodingCount P := by
  have hd := List.take_append_drop i.val P.types
  have heq := congrArg (fun xs : List LabelType =>
    (xs.map (fun t => (if t=LabelType.contraction then 2 else 1 : ℕ))).sum) hd
  rw [List.drop_eq_getElem_cons i.isLt,ht] at heq
  simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,ite_true] at heq
  change ((P.types.take i.val).map (fun t => (if t=LabelType.contraction then 2 else 1 : ℕ))).sum+1<
    (P.types.map (fun t => (if t=LabelType.contraction then 2 else 1 : ℕ))).sum
  omega

 theorem eval_label {P : Presentation} (R : StructuralRealization P) (k : ℕ) (hk : k<5)
    (i : Fin P.types.length) :
    evalPoly (dictionary R) (labelCopy P k i.val)=
      lift 17 (selected k) (selected k) (labelExtension R i.val) := by
  rw [eval_labelCopy,eval_e R k hk,dictionary_copy R k _ hk (offset_lt P i)]
  have ht : (P.types[i.val]?).getD .unitary=P.types[i.val] := by simp
  rw [ht]
  have hfull := decode_copy (selected k) (encoding R (encodingOffset P i.val))
    (encoding R (encodingOffset P i.val+1)) P.types[i.val]
  dsimp only [labelExtension]
  rw [ht]
  cases he : P.types[i.val]
  · simpa only [he,decodeEncoding] using hfull
  · simpa only [he,decodeEncoding] using hfull
  · simpa only [he,decodeEncoding] using hfull
  · rw [dictionary_copy R k _ hk (second_lt P i he)]
    simpa only [he] using hfull

 theorem expression_lift {P : Presentation} (R : StructuralRealization P)
    (k : ℕ) (hk : k<5) (p : Expr) (hp : ∀ i ∈ p.labels,i<P.types.length) :
    evalPoly (dictionary R) (expression P k p)=
      lift 17 (selected k) (selected k) (p.eval 1 (labelExtension R)) := by
  rw [evalPoly_expression]
  induction p with
  | scalar q =>
      simp only [Expr.eval]
      rw [eval_e R k hk,corner_lift,← lift_smul]
  | label i =>
      simp only [Expr.eval]
      exact eval_label R k hk ⟨i,hp i (by simp [Expr.labels])⟩
  | add p q ihp ihq =>
      simp only [Expr.eval]
      rw [ihp (fun i hi => hp i (by simp [Expr.labels,hi])),
        ihq (fun i hi => hp i (by simp [Expr.labels,hi])),lift_add]
  | mul p q ihp ihq =>
      simp only [Expr.eval]
      rw [ihp (fun i hi => hp i (by simp [Expr.labels,hi])),
        ihq (fun i hi => hp i (by simp [Expr.labels,hi])),lift_mul,if_pos rfl]
  | adj p ih =>
      simp only [Expr.eval]
      rw [ih hp,lift_star]

 theorem expression_compress {P : Presentation} (R : StructuralRealization P)
    (p : Expr) (hp : ∀ i ∈ p.labels,i<P.types.length) :
    R.support*p.eval 1 (labelExtension R)=p.eval R.support R.label ∧
    p.eval 1 (labelExtension R)*R.support=p.eval R.support R.label := by
  induction p with
  | scalar q =>
      simp [Expr.eval,mul_smul_comm,smul_mul_assoc]
  | label i => exact labelExtension_compress R ⟨i,hp i (by simp [Expr.labels])⟩
  | add p q ihp ihq =>
      obtain ⟨hpl,hpr⟩ := ihp (fun i hi => hp i (by simp [Expr.labels,hi]))
      obtain ⟨hql,hqr⟩ := ihq (fun i hi => hp i (by simp [Expr.labels,hi]))
      simp only [Expr.eval,mul_add,add_mul,hpl,hpr,hql,hqr,and_self]
  | mul p q ihp ihq =>
      obtain ⟨hpl,hpr⟩ := ihp (fun i hi => hp i (by simp [Expr.labels,hi]))
      obtain ⟨hql,hqr⟩ := ihq (fun i hi => hp i (by simp [Expr.labels,hi]))
      have hpe : p.eval R.support R.label*R.support=p.eval R.support R.label := by
        calc
          _=(p.eval 1 (labelExtension R)*R.support)*R.support := by rw [hpr]
          _=p.eval 1 (labelExtension R)*(R.support*R.support) := mul_assoc _ _ _
          _=_ := by rw [R.support_projection.2,hpr]
      have hqe : R.support*q.eval R.support R.label=q.eval R.support R.label := by
        calc
          _=R.support*(R.support*q.eval 1 (labelExtension R)) := by rw [hql]
          _=(R.support*R.support)*q.eval 1 (labelExtension R) := (mul_assoc _ _ _).symm
          _=_ := by rw [R.support_projection.2,hql]
      constructor
      · change R.support*(p.eval 1 (labelExtension R)*q.eval 1 (labelExtension R))=_
        rw [← mul_assoc,hpl,← hpe,mul_assoc,hql]
        rfl
      · change (p.eval 1 (labelExtension R)*q.eval 1 (labelExtension R))*R.support=_
        rw [mul_assoc,hqr,← hqe,← mul_assoc,hpr]
        rfl
  | adj p ih =>
      obtain ⟨hl,hr⟩ := ih hp
      constructor
      · have ht := congrArg (fun A : Op => star A) hr
        simpa only [Expr.eval,star_mul,R.support_projection.1] using ht
      · have ht := congrArg (fun A : Op => star A) hl
        simpa only [Expr.eval,star_mul,R.support_projection.1] using ht

#print axioms eval_label
#print axioms expression_lift
#print axioms expression_compress
end Sigma2.CompilerApproxLabels
