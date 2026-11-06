import Sigma2.CompilerApproxLabels

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxResidual
open Compiler CompilerScaffold CompilerHonestDictionary CompilerFiniteRegister
  CompilerHonestLift CompilerHonestLabels CompilerHonestSyntax FiniteAncilla
  CompilerApproxDictionary CompilerApproxLabels CompilerHonestDensity CompilerApproxBlocks

 theorem lift_sub (d : ℕ) [NeZero d] (a b : Fin d) (A B : Op) :
    lift d a b (A-B)=lift d a b A-lift d a b B := by
  simpa only [neg_one_smul ℂ B,neg_one_smul ℂ (lift d a b B),sub_eq_add_neg] using
    (show lift d a b (A+(-1:ℂ) • B)=lift d a b A+(-1:ℂ) • lift d a b B by rw [lift_add,lift_smul])

 theorem lift_amplify (d : ℕ) [NeZero d] (a b : Fin d) (A e : Op) :
    lift d a b A*amplify d e=lift d a b (A*e) := by
  ext v : 1
  apply FiniteSum.ext_fiber (coordinates d)
  intro i
  rw [mul_apply_eq_comp,lift_fiber,lift_fiber,fiber_amplify]
  split_ifs <;> rfl

 theorem lift_fin_sum {ι : Type} [Fintype ι] (d : ℕ) [NeZero d] (a b : Fin d) (A : ι → Op) :
    lift d a b (∑ i,A i)=∑ i,lift d a b (A i) := by
  classical
  generalize (Finset.univ : Finset ι)=s
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi,lift_add,ih]

 theorem lift_list_sum (d : ℕ) [NeZero d] (a b : Fin d) (xs : List Op) :
    lift d a b xs.sum=(xs.map (lift d a b)).sum := by
  induction xs with
  | nil => simp
  | cons A xs ih => simp only [List.sum_cons,List.map_cons,lift_add,ih]

 theorem eval_sum (U : ℕ → Op) (ps : List Poly) :
    evalPoly U (sum ps)=(ps.map (evalPoly U)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa only [sum,List.flatten_cons,List.map_cons,List.sum_cons,evalPoly_append] using
      (congrArg (fun A : Op => evalPoly U p+A) ih)

 theorem compress_energy (h : Density) (e A : Op) (he : Projection e)
    (hh : e*h.op=h.op) : trace (h.op*(star (A*e)*(A*e)))=trace (h.op*(star A*A)) := by
  have hhr : h.op*e=h.op := by
    have ht := congrArg (fun B : Op => star B) hh
    simpa only [star_mul,he.1,h.positive.isSelfAdjoint.star_eq] using ht
  rw [← CompilerApproxQutrit.trace_transport h (A*e),
    ← CompilerApproxQutrit.trace_transport h A,star_mul,he.1]
  congr 1
  simp only [mul_assoc,hh]
  rw [← mul_assoc h.op e, hhr]

 theorem creation_right {P : Presentation} (R : StructuralRealization P) (a b : Fin 4) :
    (star (R.creation a)*R.creation b)*R.support=star (R.creation a)*R.creation b := by
  rw [mul_assoc,(R.creation_supported b).2]

 theorem range_right {P : Presentation} (R : StructuralRealization P) :
    (∑ a,R.creation a*star (R.creation a))*R.support=∑ a,R.creation a*star (R.creation a) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hs : star (R.creation a)*R.support=star (R.creation a) := by
    have ht := congrArg (fun A : Op => star A) (R.creation_supported a).1
    simpa only [star_mul,R.support_projection.1] using ht
  rw [mul_assoc,hs]

 theorem left_creation {P : Presentation} (R : StructuralRealization P) (p : Expr)
    (hp : ∀ i ∈ p.labels,i<P.types.length) (a : Fin 4) :
    p.eval 1 (labelExtension R)*R.creation a=p.eval R.support R.label*R.creation a := by
  calc
    _=p.eval 1 (labelExtension R)*(R.support*R.creation a) := by rw [(R.creation_supported a).1]
    _=_ := by rw [← mul_assoc,(expression_compress R p hp).2]

 theorem isometry_compress {P : Presentation} (R : StructuralRealization P) (a b : Fin 4) :
    evalPoly (dictionary R) (sub (mul (adj (creation P a.val)) (creation P b.val))
      (if a.val=b.val then e 0 else []))*amplify 17 R.support=
    lift 17 0 0 (star (R.creation a)*R.creation b-(if a=b then R.support else 0)) := by
  rw [evalPoly_sub,evalPoly_mul,eval_adj,eval_creation R a,eval_creation R b,
    lift_star,lift_mul,if_pos rfl]
  have he : evalPoly (dictionary R) (e 0)=lift 17 0 0 1 := by
    rw [eval_e R 0 (by omega),corner_lift]; rfl
  by_cases hab : a=b
  · subst b
    rw [if_pos rfl,he,← lift_sub,lift_amplify,sub_mul,creation_right,one_mul,if_pos rfl]
  · have hv : a.val≠b.val := by exact fun h => hab (Fin.ext h)
    rw [if_neg hv,if_neg hab]
    change (lift 17 0 0 (star (R.creation a)*R.creation b)-0)*_=lift 17 0 0 (_-0)
    rw [sub_zero,sub_zero,lift_amplify,creation_right]

 theorem range_compress {P : Presentation} (R : StructuralRealization P)
    (hr : P.root<P.types.length) :
    evalPoly (dictionary R)
      (sub (sum ((List.range 4).map (fun a => mul (creation P a) (adj (creation P a)))))
        (sub (e 4) (labelCopy P 4 P.root)))*amplify 17 R.support=
    lift 17 13 13 ((∑ a,R.creation a*star (R.creation a))-(R.support-R.label P.root)) := by
  have hsum : evalPoly (dictionary R)
      (sum ((List.range 4).map (fun a => mul (creation P a) (adj (creation P a)))))=
      lift 17 13 13 (∑ a,R.creation a*star (R.creation a)) := by
    rw [eval_sum]
    simp only [List.map_map,Function.comp_def]
    have he : (List.range 4).map (fun a => evalPoly (dictionary R) (mul (creation P a) (adj (creation P a))))=
        List.ofFn (fun a : Fin 4 => evalPoly (dictionary R) (mul (creation P a.val) (adj (creation P a.val)))) := by rfl
    rw [he,List.sum_ofFn,lift_fin_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [evalPoly_mul,eval_adj,eval_creation R a,lift_star,lift_mul,if_pos rfl]
  rw [evalPoly_sub,hsum,evalPoly_sub,eval_e R 4 (by omega),corner_lift,eval_label R 4 (by omega) ⟨P.root,hr⟩]
  change (lift 17 13 13 _-(lift 17 13 13 1-lift 17 13 13 _))*_=_
  rw [← lift_sub,← lift_sub,lift_amplify,sub_mul,sub_mul,one_mul,range_right,
    (labelExtension_compress R ⟨P.root,hr⟩).2]

 theorem central_compress {P : Presentation} (R : StructuralRealization P) (p : Expr)
    (hp : ∀ i ∈ p.labels,i<P.types.length) :
    evalPoly (dictionary R) (expression P 0 p)*amplify 17 R.support=
      lift 17 0 0 (p.eval R.support R.label) := by
  rw [expression_lift R 0 (by omega) p hp]
  change lift 17 0 0 _*_=lift 17 0 0 _
  rw [lift_amplify,(expression_compress R p hp).2]

 theorem endpoint_compress {P : Presentation} (R : StructuralRealization P)
    (p q : Expr) (a b : Fin 4)
    (hp : ∀ i ∈ p.labels,i<P.types.length) (hq : ∀ i ∈ q.labels,i<P.types.length) :
    evalPoly (dictionary R) (sub (mul (expression P 4 p) (creation P a.val))
      (mul (creation P b.val) (expression P 0 q)))*amplify 17 R.support=
    lift 17 13 0 (p.eval R.support R.label*R.creation a-R.creation b*q.eval R.support R.label) := by
  rw [evalPoly_sub,evalPoly_mul,evalPoly_mul,expression_lift R 4 (by omega) p hp,
    expression_lift R 0 (by omega) q hq,eval_creation R a,eval_creation R b]
  change (lift 17 13 13 _*lift 17 13 0 _-lift 17 13 0 _*lift 17 0 0 _)*_=_
  rw [lift_mul,if_pos rfl,lift_mul,if_pos rfl,← lift_sub,lift_amplify,sub_mul,
    mul_assoc,(R.creation_supported a).2,left_creation R p hp a,mul_assoc,
    (expression_compress R q hq).2]

 theorem zero_compress {P : Presentation} (R : StructuralRealization P)
    (p : Expr) (a : Fin 4) (hp : ∀ i ∈ p.labels,i<P.types.length) :
    evalPoly (dictionary R) (mul (expression P 4 p) (creation P a.val))*amplify 17 R.support=
    lift 17 13 0 (p.eval R.support R.label*R.creation a) := by
  rw [evalPoly_mul,expression_lift R 4 (by omega) p hp,eval_creation R a]
  change (lift 17 13 13 _*lift 17 13 0 _)*_=_
  rw [lift_mul,if_pos rfl,lift_amplify,mul_assoc,(R.creation_supported a).2,left_creation R p hp a]

 theorem linear_term_compress {P : Presentation} (R : StructuralRealization P)
    (p q : Expr) (a : Fin 4)
    (hp : ∀ i ∈ p.labels,i<P.types.length) (hq : ∀ i ∈ q.labels,i<P.types.length) :
    evalPoly (dictionary R) (mul (mul (expression P 4 p) (creation P a.val)) (expression P 0 q))*
      amplify 17 R.support=
    lift 17 13 0 (p.eval R.support R.label*R.creation a*q.eval R.support R.label) := by
  rw [evalPoly_mul,evalPoly_mul,expression_lift R 4 (by omega) p hp,
    expression_lift R 0 (by omega) q hq,eval_creation R a]
  change ((lift 17 13 13 _*lift 17 13 0 _)*lift 17 0 0 _)*_=_
  rw [lift_mul,if_pos rfl,lift_mul,if_pos rfl,lift_amplify,mul_assoc,
    (expression_compress R q hq).2,left_creation R p hp a]

#print axioms compress_energy
#print axioms isometry_compress
#print axioms range_compress
#print axioms central_compress
#print axioms endpoint_compress
#print axioms zero_compress
#print axioms linear_term_compress
end Sigma2.CompilerApproxResidual
