import Sigma2.CompilerSoundnessTyping

/-! Actual application rows, evaluated in the same full-support dictionary. -/
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessApplications
open Compiler CompilerScaffold CompilerSoundnessExtraction CompilerSoundnessLift
  CompilerSoundnessDictionary CompilerSoundnessIntertwiners CompilerSoundnessBridgeCopies
  CompilerSoundnessLabels CompilerSoundnessChain CompilerSoundnessSourceOperators Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

theorem fullValue_nil (E : SupportedScaffold P) : fullValue E []=0 := by
  simp [fullValue,CompilerSoundnessBlockEquations.value,CompilerScaffold.evalPoly,spread_zero]

theorem application_equation (E : SupportedScaffold P) (p : Poly)
    (hp : p ∈ applicationPolynomials P) : fullValue E p=0 :=
  full_polynomial_equations E p (by simp only [polynomials,List.mem_append]; exact Or.inr hp)

theorem submitted_isometries (E : SupportedScaffold P) (a b : Fin 4) :
    star (submittedCreation E a)*submittedCreation E b=if a=b then corner E 0 else 0 := by
  have hm : sub (mul (adj (creation P a.val)) (creation P b.val))
      (if a.val=b.val then e 0 else []) ∈ applicationPolynomials P := by
    have hm : sub (mul (adj (creation P a.val)) (creation P b.val))
        (if a.val=b.val then e 0 else []) ∈
        (List.range 4).flatMap (fun a => (List.range 4).map (fun b =>
          sub (mul (adj (creation P a)) (creation P b)) (if a=b then e 0 else []))) :=
      List.mem_flatMap.mpr ⟨a.val,List.mem_range.mpr a.isLt,
        List.mem_map.mpr ⟨b.val,List.mem_range.mpr b.isLt,rfl⟩⟩
    simp only [applicationPolynomials,List.mem_append]; tauto
  have hp := application_equation E _ hm
  rw [fullValue_sub,fullValue_mul,fullValue_adj] at hp
  have hh := sub_eq_zero.mp hp
  change star (submittedCreation E a)*submittedCreation E b=_ at hh
  rw [hh]
  by_cases hab : a=b
  · subst b
    rw [if_pos rfl,if_pos rfl,fullValue_e E ⟨0,by decide⟩]
    rfl
  · rw [if_neg hab,if_neg (fun h => hab (Fin.ext h)),fullValue_nil]

theorem range_row (P : Presentation) :
    sub (CompilerScaffold.sum ((List.range 4).map (fun a => mul (creation P a) (adj (creation P a)))))
      (sub (e 4) (labelCopy P 4 P.root)) ∈ applicationPolynomials P := by
  simp only [applicationPolynomials,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  tauto

theorem submitted_ranges (E : SupportedScaffold P) :
    (∑ a : Fin 4,submittedCreation E a*star (submittedCreation E a))=corner E 4-label E 4 P.root := by
  have hp := application_equation E _ (range_row P)
  rw [fullValue_sub,fullValue_sub,fullValue_e E ⟨4,by decide⟩,fullValue_sum,List.map_map] at hp
  have hh := sub_eq_zero.mp hp
  convert hh using 1
  simp only [Function.comp_def,fullValue_mul,fullValue_adj]
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,add_zero,zero_add,Fin.sum_univ_four,submittedCreation]
  all_goals rfl

theorem returned_isometries (E : SupportedScaffold P) (a b : Fin 4) :
    star (returnedCreation E a)*returnedCreation E b=if a=b then corner E 0 else 0 := by
  unfold returnedCreation
  rw [star_mul,star_star]
  calc
    _=star (submittedCreation E a)*(chain E*star (chain E))*submittedCreation E b := by simp only [mul_assoc]
    _=star (submittedCreation E a)*submittedCreation E b := by
      rw [(chain_partial E).final,mul_assoc,(submittedCreation_supported E b).1]
    _=_ := submitted_isometries E a b

theorem source_eval (E : SupportedScaffold P) (p : Expr)
    (hp : ∀ i ∈ p.labels,i<P.types.length) :
    fullValue E (expression P 0 p)=p.eval (corner E 0) (returnedLabel E) := by
  rw [fullValue_expression E ⟨0,by decide⟩]
  induction p with
  | scalar q => rfl
  | label i =>
    have hi := hp i (by simp [Expr.labels])
    simp only [Expr.eval,returnedLabel,if_pos hi,label]
  | add p q ihp ihq =>
    have h : (∀ i ∈ p.labels,i<P.types.length) ∧ (∀ i ∈ q.labels,i<P.types.length) := ⟨fun i hi => hp i (List.mem_append_left _ hi),fun i hi => hp i (List.mem_append_right _ hi)⟩
    exact congrArg₂ (·+·) (ihp h.1) (ihq h.2)
  | mul p q ihp ihq =>
    have h : (∀ i ∈ p.labels,i<P.types.length) ∧ (∀ i ∈ q.labels,i<P.types.length) := ⟨fun i hi => hp i (List.mem_append_left _ hi),fun i hi => hp i (List.mem_append_right _ hi)⟩
    exact congrArg₂ (·*·) (ihp h.1) (ihq h.2)
  | adj p ih => exact congrArg (fun A : Op => star A) (ih hp)

theorem expression_transport (E : SupportedScaffold P) (p : Expr)
    (hp : ∀ i ∈ p.labels,i<P.types.length) :
    fullValue E (expression P 4 p)*chain E=chain E*fullValue E (expression P 0 p) ∧
    star (fullValue E (expression P 4 p))*chain E=chain E*star (fullValue E (expression P 0 p)) := by
  induction p with
  | scalar q =>
    have h0 : fullValue E (e 0)=corner E 0 := fullValue_e E 0
    have h4 : fullValue E (e 4)=corner E 4 := fullValue_e E 4
    simp only [expression,fullValue_scale,h4,h0]
    constructor
    · simp only [smul_mul_assoc,mul_smul_comm,(chain_partial E).left,(chain_partial E).right]
    · simp only [PauliMatrixUnits.op_star_smul,star_ratCast,(corner_projection E 4).1,(corner_projection E 0).1,
        smul_mul_assoc,mul_smul_comm,(chain_partial E).left,(chain_partial E).right]
  | label i =>
    have hi := hp i (by simp [Expr.labels])
    exact ⟨label_chain E ⟨i,hi⟩,label_adjoint_chain E ⟨i,hi⟩⟩
  | add p q ihp ihq =>
    have h : (∀ i ∈ p.labels,i<P.types.length) ∧ (∀ i ∈ q.labels,i<P.types.length) := ⟨fun i hi => hp i (List.mem_append_left _ hi),fun i hi => hp i (List.mem_append_right _ hi)⟩
    have hp := ihp h.1; have hq := ihq h.2
    simp only [expression,fullValue_append,PauliMatrixUnits.op_star_add,add_mul,mul_add,hp.1,hq.1,hp.2,hq.2,and_self]
  | mul p q ihp ihq =>
    have h : (∀ i ∈ p.labels,i<P.types.length) ∧ (∀ i ∈ q.labels,i<P.types.length) := ⟨fun i hi => hp i (List.mem_append_left _ hi),fun i hi => hp i (List.mem_append_right _ hi)⟩
    have hp := ihp h.1; have hq := ihq h.2
    simp only [expression,fullValue_mul,star_mul]
    constructor
    · rw [mul_assoc,hq.1,← mul_assoc,hp.1,mul_assoc]
    · rw [mul_assoc,hp.2,← mul_assoc,hq.2,mul_assoc]
  | adj p ih =>
    have h := ih hp
    simp only [expression,fullValue_adj,star_star]
    exact ⟨h.2,h.1⟩

theorem expression_return (E : SupportedScaffold P) (p : Expr)
    (hp : ∀ i ∈ p.labels,i<P.types.length) :
    star (chain E)*fullValue E (expression P 4 p)=
      p.eval (corner E 0) (returnedLabel E)*star (chain E) := by
  have h := congrArg (fun A : Op => star A) (expression_transport E p hp).2
  simpa only [star_mul,star_star,source_eval E p hp] using h

theorem returned_ranges (E : SupportedScaffold P) (hroot : P.root<P.types.length) :
    (∑ a,returnedCreation E a*star (returnedCreation E a))=corner E 0-returnedLabel E P.root := by
  have hl : label E 4 P.root*chain E=chain E*returnedLabel E P.root := by
    simpa only [returnedLabel,if_pos hroot] using label_chain E ⟨_,hroot⟩
  have hs : corner E 0*returnedLabel E P.root=returnedLabel E P.root := (returnedLabel_supported E _).1
  calc
    _=star (chain E)*(∑ a : Fin 4,submittedCreation E a*star (submittedCreation E a))*chain E := by
      simp only [returnedCreation,star_mul,star_star,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _=star (chain E)*(corner E 4-label E 4 P.root)*chain E := by rw [submitted_ranges]
    _=corner E 0-returnedLabel E P.root := by
      rw [mul_sub,sub_mul,mul_assoc,(chain_partial E).left,(chain_partial E).initial,
        mul_assoc,hl,← mul_assoc,(chain_partial E).initial,hs]

theorem central_equation (E : SupportedScaffold P) (p : Expr) (hm : p ∈ P.central)
    (hp : ∀ i ∈ p.labels,i<P.types.length) : p.eval (corner E 0) (returnedLabel E)=0 := by
  rw [← source_eval E p hp]
  apply application_equation
  have h : expression P 0 p ∈ P.central.map (expression P 0) := List.mem_map.mpr ⟨p,hm,rfl⟩
  simp only [applicationPolynomials,List.mem_append]; tauto

theorem endpoint_equation (E : SupportedScaffold P)
    (r : Expr × Fin 4 × Fin 4 × Expr) (hr : r ∈ P.endpoints)
    (hp : ∀ i ∈ r.1.labels,i<P.types.length)
    (hq : ∀ i ∈ r.2.2.2.labels,i<P.types.length) :
    r.1.eval (corner E 0) (returnedLabel E)*returnedCreation E r.2.1=
      returnedCreation E r.2.2.1*r.2.2.2.eval (corner E 0) (returnedLabel E) := by
  have hm : sub (mul (expression P 4 r.1) (creation P r.2.1.val))
      (mul (creation P r.2.2.1.val) (expression P 0 r.2.2.2)) ∈ applicationPolynomials P := by
    have h : sub (mul (expression P 4 r.1) (creation P r.2.1.val))
        (mul (creation P r.2.2.1.val) (expression P 0 r.2.2.2)) ∈
        P.endpoints.map (fun r => sub (mul (expression P 4 r.1) (creation P r.2.1.val))
          (mul (creation P r.2.2.1.val) (expression P 0 r.2.2.2))) := List.mem_map.mpr ⟨r,hr,rfl⟩
    simp only [applicationPolynomials,List.mem_append]; tauto
  have h := application_equation E _ hm
  rw [fullValue_sub,fullValue_mul,fullValue_mul,source_eval E _ hq] at h
  have hh := congrArg (fun A : Op => star (chain E)*A) (sub_eq_zero.mp h)
  rw [← mul_assoc,expression_return E _ hp] at hh
  simpa only [returnedCreation,mul_assoc,submittedCreation] using hh

theorem zero_equation (E : SupportedScaffold P) (r : Expr × Fin 4) (hr : r ∈ P.zeros)
    (hp : ∀ i ∈ r.1.labels,i<P.types.length) :
    r.1.eval (corner E 0) (returnedLabel E)*returnedCreation E r.2=0 := by
  have hm : mul (expression P 4 r.1) (creation P r.2.val) ∈ applicationPolynomials P := by
    have h : mul (expression P 4 r.1) (creation P r.2.val) ∈
        P.zeros.map (fun r => mul (expression P 4 r.1) (creation P r.2.val)) := List.mem_map.mpr ⟨r,hr,rfl⟩
    simp only [applicationPolynomials,List.mem_append]; tauto
  have h := application_equation E _ hm
  rw [fullValue_mul] at h
  have hh := congrArg (fun A : Op => star (chain E)*A) h
  rw [← mul_assoc,expression_return E _ hp,mul_zero] at hh
  simpa only [returnedCreation,submittedCreation,mul_assoc] using hh

theorem mul_list_sum (A : Op) (xs : List Op) : A*xs.sum=(xs.map (fun X => A*X)).sum := by
  induction xs with
  | nil => simp
  | cons X xs ih => simp only [List.sum_cons,List.map_cons,mul_add,ih]

theorem linear_equation (E : SupportedScaffold P) (row : List (Expr × Fin 4 × Expr))
    (hr : row ∈ P.linear)
    (hp : ∀ r ∈ row,(∀ i ∈ r.1.labels,i<P.types.length) ∧ (∀ i ∈ r.2.2.labels,i<P.types.length)) :
    (row.map (fun r => r.1.eval (corner E 0) (returnedLabel E)*returnedCreation E r.2.1*
      r.2.2.eval (corner E 0) (returnedLabel E))).sum=0 := by
  have hm : CompilerScaffold.sum (row.map (fun r =>
      mul (mul (expression P 4 r.1) (creation P r.2.1.val)) (expression P 0 r.2.2))) ∈ applicationPolynomials P := by
    have h : CompilerScaffold.sum (row.map (fun r => mul (mul (expression P 4 r.1)
        (creation P r.2.1.val)) (expression P 0 r.2.2))) ∈
        P.linear.map (fun row => CompilerScaffold.sum (row.map (fun r => mul (mul (expression P 4 r.1)
          (creation P r.2.1.val)) (expression P 0 r.2.2)))) := List.mem_map.mpr ⟨row,hr,rfl⟩
    simp only [applicationPolynomials,List.mem_append]; tauto
  have h := application_equation E _ hm
  rw [fullValue_sum,List.map_map] at h
  have hh := congrArg (fun A : Op => star (chain E)*A) h
  rw [mul_list_sum,List.map_map,mul_zero] at hh
  convert hh using 1
  congr 1
  apply List.map_congr_left
  intro r hr
  dsimp only [Function.comp_def]
  rw [fullValue_mul,fullValue_mul,source_eval E _ (hp r hr).2,← mul_assoc,← mul_assoc,
    expression_return E _ (hp r hr).1]
  simp only [returnedCreation,submittedCreation,mul_assoc]

#print axioms returned_isometries
#print axioms returned_ranges
#print axioms expression_transport
end Sigma2.CompilerSoundnessApplications
