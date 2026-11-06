import Sigma2.CompilerSoundnessParameters

/-! Decode the actual joint graph/parameter rows on the extracted support. -/
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessJoints
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessFrame CompilerSoundnessGraphs CompilerSoundnessParameters Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
  CompilerScaffold.bindingRows

theorem projection_positive (A : Op) (hA : Projection A) : Positive A :=
  ContinuousLinearMap.IsPositive.of_isStarProjection ⟨hA.2,hA.1⟩

theorem orthogonal_sum (A B : Op) (hA : Projection A) (hB : Projection B)
    (hab : A*B=0) : Projection (A+B) := by
  have hba : B*A=0 := by
    simpa only [star_mul,hA.1,hB.1,show star (0:Op)=0 from star_zero Op] using congrArg (fun X : Op => star X) hab
  exact ⟨by rw [star_add A B,hA.1,hB.1],by rw [add_mul,mul_add,mul_add,hA.2,hB.2,hab,hba]; abel⟩

/-- A four-cell sharp joint measurement also decodes its equality outcome.
The identity may be a support projection. -/
theorem joint_decode (E A G H : Op) (J : Fin 4 → Op)
    (he : Projection E) (ha : Projection A) (hg : Projection G)
    (hj : ∀ i,Positive (J i))
    (h1 : J 0+J 1=A) (h0 : J 2+J 3=E-A)
    (hG : J 0+J 3=G) (hH : J 0+J 2=H) :
    A*G=G*A ∧ H=E-A-G+(2:ℂ) • (A*G) := by
  have hs : ∑ i,J i=E := by
    simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.coe_ofNat_eq_mod,Fin.isValue] at *
    calc
      J 0+(J 1+(J 2+(J 3+0)))=(J 0+J 1)+(J 2+J 3) := by abel
      _=E := by rw [h1,h0]; abel
  let mask : Fin 4 → Bool := fun i => decide (i.val<2)
  have hc : CoarseCells.coarse J mask true=A := by
    norm_num [CoarseCells.coarse,mask,Fin.sum_univ_succ]
    exact h1
  have act (i : Fin 4) : A*J i=if i.val<2 then J i else 0 := by
    have hh := FiniteSpectral.coarse_action J mask true E he hj hs (by rw [hc]; exact ha) i
    simpa only [hc,mask,decide_eq_true_eq] using hh
  have hAG : A*G=J 0 := by rw [← hG,mul_add,act,act]; norm_num
  have hGA : G*A=J 0 := by
    have hself : star (J 0)=J 0 := (hj 0).isSelfAdjoint
    simpa only [star_mul,ha.1,hg.1,hself] using congrArg (fun X : Op => star X) hAG
  refine ⟨hAG.trans hGA.symm,?_⟩
  rw [hAG,← hH,← hG,← h1] at *
  calc
    J 0+J 2 = (J 2+J 3)-(J 0+J 3)+(2:ℂ) • J 0 := by module
    _ = E-(J 0+J 1)-(J 0+J 3)+(2:ℂ) • J 0 := by rw [h0]

theorem joint_equations (P : Presentation) (e : Op) (F : ProjectionName → Op)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0) (p : Fin 25) (k : Fin 3) :
    let ij := pairs[k.val]?.getD (0,1)
    F (.joint p.val k.val 1 1)+F (.joint p.val k.val 1 0)=
      F (.binding p.val ij.1 false)+F (.binding p.val ij.2 false) ∧
    F (.joint p.val k.val 0 0)+F (.joint p.val k.val 0 1)=
      F (.binding p.val ij.1 true)+F (.binding p.val ij.2 true) ∧
    F (.joint p.val k.val 1 1)+F (.joint p.val k.val 0 1)=F (.graph [] k.val 0) ∧
    F (.joint p.val k.val 1 1)+F (.joint p.val k.val 0 0)=F (.graph [(p.val,false)] k.val 0) := by
  let ij := pairs[k.val]?.getD (0,1)
  have all (r : RationalRow) (hr : r ∈
      [row [(1,.joint p.val k.val 1 1),(1,.joint p.val k.val 1 0),(-1,.binding p.val ij.1 false),(-1,.binding p.val ij.2 false)],
       row [(1,.joint p.val k.val 0 0),(1,.joint p.val k.val 0 1),(-1,.binding p.val ij.1 true),(-1,.binding p.val ij.2 true)],
       row [(1,.joint p.val k.val 1 1),(1,.joint p.val k.val 0 1),(-1,.graph [] k.val 0)],
       row [(1,.graph [(p.val,false)] k.val 0),(-1,.joint p.val k.val 1 1),(-1,.joint p.val k.val 0 0)]]) : evalRow e F r=0 := by
    apply hrows r
    apply bindingRow_mem P p r
    simp only [bindingRows,List.mem_append]
    right
    exact List.mem_flatMap.mpr ⟨k.val,List.mem_range.mpr k.isLt,hr⟩
  have h1 := all _ (by simp only [List.mem_cons]; exact Or.inl rfl)
  have h0 := all _ (by simp only [List.mem_cons]; exact Or.inr (Or.inl rfl))
  have hg := all _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inl rfl)))
  have hh := all _ (by simp only [List.mem_cons]; exact Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  refine ⟨?_,?_,?_,?_⟩
  all_goals apply sub_eq_zero.mp
  · calc
      _=evalRow e F (row [(1,.joint p.val k.val 1 1),(1,.joint p.val k.val 1 0),(-1,.binding p.val ij.1 false),(-1,.binding p.val ij.2 false)]) := by simp [evalRow,row]; module
      _=0 := h1
  · calc
      _=evalRow e F (row [(1,.joint p.val k.val 0 0),(1,.joint p.val k.val 0 1),(-1,.binding p.val ij.1 true),(-1,.binding p.val ij.2 true)]) := by simp [evalRow,row]; module
      _=0 := h0
  · calc
      _=evalRow e F (row [(1,.joint p.val k.val 1 1),(1,.joint p.val k.val 0 1),(-1,.graph [] k.val 0)]) := by simp [evalRow,row]; module
      _=0 := hg
  · calc
      _= -evalRow e F (row [(1,.graph [(p.val,false)] k.val 0),(-1,.joint p.val k.val 1 1),(-1,.joint p.val k.val 0 0)]) := by simp [evalRow,row]; module
      _=0 := by rw [hh,neg_zero]


theorem empty_mem_words (P : Presentation) : [] ∈ words P := by
  simp only [words,List.mem_dedup]
  exact List.mem_cons_self ..

theorem pair_bounds (k : Fin 3) :
    (pairs[k.val]?.getD (0,1)).1<3 ∧ (pairs[k.val]?.getD (0,1)).2<3 ∧
      (pairs[k.val]?.getD (0,1)).1≠(pairs[k.val]?.getD (0,1)).2 := by
  fin_cases k <;> decide

/-- The submitted parameter graph is the signed joint graph, and the same
parameter commutes with the empty graph. -/
theorem parameter_graph (P : Presentation) (e : Op) (F : ProjectionName → Op)
    (hp : ∀ n,Projection (F n))
    (hframe : ∀ i j : Fin 3,F (.frame i.val)*F (.frame j.val)=
      if i=j then F (.frame j.val) else 0)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0) (p : Fin 25) (k : Fin 3) :
    Commute (F (.parameter p.val)) (F (.graph [] k.val 0)) ∧
    graphBlock F [(p.val,false)] k.val=
      (2:ℂ) • (F (.parameter p.val)*graphBlock F [] k.val)-graphBlock F [] k.val ∧
    Commute (F (.parameter p.val)) (graphBlock F [] k.val) := by
  let ij := pairs[k.val]?.getD (0,1)
  let i : Fin 3 := ⟨ij.1,(pair_bounds k).1⟩
  let j : Fin 3 := ⟨ij.2,(pair_bounds k).2.1⟩
  let Fi := F (.frame ij.1)
  let Fj := F (.frame ij.2)
  let E := Fi+Fj
  let C := F (.parameter p.val)
  let A := C*E
  let G := F (.graph [] k.val 0)
  let H := F (.graph [(p.val,false)] k.val 0)
  have hci : C*Fi=Fi*C := by
    have hh := parameter_frame_action e F hp hframe p.val
      (binding_equations P e F hrows p).1 (binding_equations P e F hrows p).2 i
    exact hh.1.trans hh.2.symm
  have hcj : C*Fj=Fj*C := by
    have hh := parameter_frame_action e F hp hframe p.val
      (binding_equations P e F hrows p).1 (binding_equations P e F hrows p).2 j
    exact hh.1.trans hh.2.symm
  have horth : Fi*Fj=0 := by
    exact (hframe i j).trans (if_neg (by intro h; exact (pair_bounds k).2.2 (congrArg Fin.val h)))
  have hE : Projection E := orthogonal_sum Fi Fj (hp _) (hp _) horth
  have hcE : C*E=E*C := by dsimp [E]; rw [mul_add,add_mul,hci,hcj]
  have hA : Projection A := projection_product C E (hp _) hE hcE
  have hb := binding_equations P e F hrows p
  have hai := parameter_frame_action e F hp hframe p.val hb.1 hb.2 i
  have haj := parameter_frame_action e F hp hframe p.val hb.1 hb.2 j
  have ha : A=F (.binding p.val ij.1 false)+F (.binding p.val ij.2 false) := by
    change C*(Fi+Fj)=_
    rw [mul_add,hai.1,haj.1]
  have hac : E-A=F (.binding p.val ij.1 true)+F (.binding p.val ij.2 true) := by
    have hi := hb.1 i
    have hj := hb.1 j
    change F (.binding p.val ij.1 false)+F (.binding p.val ij.1 true)=Fi at hi
    change F (.binding p.val ij.2 false)+F (.binding p.val ij.2 true)=Fj at hj
    rw [ha]
    dsimp [E]
    rw [← hi,← hj]
    abel
  let J : Fin 4 → Op := ![F (.joint p.val k.val 1 1),F (.joint p.val k.val 1 0),
    F (.joint p.val k.val 0 0),F (.joint p.val k.val 0 1)]
  have hjoint := joint_equations P e F hrows p k
  have hdec := joint_decode E A G H J hE hA (hp _) (fun a => by
    fin_cases a <;> exact projection_positive _ (hp _))
    (by exact hjoint.1.trans ha.symm) (by exact hjoint.2.1.trans hac.symm)
    hjoint.2.2.1 hjoint.2.2.2
  have hgr := graph_equations e F [] k.val (fun r hr =>
    hrows r (graphRow_mem P [] (empty_mem_words P) k r hr))
  have hsG : G*E=G ∧ E*G=G := by
    apply positive_below_projection G E (projection_positive _ (hp _)) hE
    change Positive ((F (.frame ij.1)+F (.frame ij.2))-F (.graph [] k.val 0))
    rw [← hgr.1,add_sub_cancel_left]
    exact projection_positive _ (hp _)
  have hAG : A*G=C*G := by dsimp [A]; rw [mul_assoc,hsG.2]
  have hGA : G*A=G*C := by
    change G*(C*E)=_
    rw [hcE,← mul_assoc,hsG.1]
  have hcG : Commute C G := by
    exact hAG.symm.trans (hdec.1.trans hGA)
  have hH : H=E-A-G+(2:ℂ) • (C*G) := by simpa only [hAG] using hdec.2
  have hFE : Fi*E=Fi := by dsimp [E]; rw [mul_add,(hp (.frame ij.1)).2,horth,add_zero]
  have hEF : E*Fj=Fj := by dsimp [E]; rw [add_mul,(hp (.frame ij.2)).2,horth,zero_add]
  have hFEF : Fi*E*Fj=0 := by rw [hFE,horth]
  have hFAF : Fi*A*Fj=0 := by
    change Fi*(C*E)*Fj=0
    calc
      _=C*(Fi*E*Fj) := by rw [← mul_assoc,← hci]; noncomm_ring
      _=0 := by rw [hFEF,mul_zero]
  have hFCG : Fi*(C*G)*Fj=C*(Fi*G*Fj) := by
    rw [← mul_assoc,← hci]
    noncomm_ring
  have hblock : graphBlock F [(p.val,false)] k.val=
      (2:ℂ) • (C*graphBlock F [] k.val)-graphBlock F [] k.val := by
    change Fi*((2:ℂ) • H-E)*Fj=
      (2:ℂ) • (C*(Fi*((2:ℂ) • G-E)*Fj))-(Fi*((2:ℂ) • G-E)*Fj)
    rw [hH]
    simp only [mul_sub,sub_mul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc,
      hFEF,hFAF,hFCG,mul_zero,smul_zero]
    module
  exact ⟨hcG,hblock,((show Commute C Fi from hci).mul_right
    ((hcG.smul_right (2:ℂ)).sub_right ((show Commute C Fi from hci).add_right hcj))).mul_right hcj⟩

#print axioms joint_decode
#print axioms joint_equations
#print axioms parameter_graph
end Sigma2.CompilerSoundnessJoints
