import Sigma2.CompilerSoundnessGraphs

/-! Recover the parameter's actual frame components from bindingRows.
No parameter/frame commutation is assumed as an external certificate. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessParameters
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows CompilerSoundnessFrame
  Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
  CompilerScaffold.bindingRows

theorem bindingRow_mem (P : Presentation) (p : Fin 25) (r : RationalRow)
    (hr : r ∈ bindingRows p.val) : r ∈ rowList P := by
  simp only [rowList,List.mem_append]
  left; left; left; right
  exact List.mem_flatMap.mpr ⟨p.val,List.mem_range.mpr p.isLt,hr⟩

theorem binding_equations (P : Presentation) (e : Op) (F : ProjectionName → Op)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0) (p : Fin 25) :
    (∀ i : Fin 3,F (.binding p.val i.val false)+F (.binding p.val i.val true)=F (.frame i.val)) ∧
      (∑ i : Fin 3,F (.binding p.val i.val false))=F (.parameter p.val) := by
  constructor
  · intro i
    let r := row [(1,.binding p.val i.val false),(1,.binding p.val i.val true),(-1,.frame i.val)]
    have hr : r ∈ bindingRows p.val := by
      unfold CompilerScaffold.bindingRows
      simp only [List.mem_append]
      left; left
      exact List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩
    apply sub_eq_zero.mp
    calc
      _ = evalRow e F r := by norm_num [evalRow,row,r] <;> module
      _ = 0 := hrows r (bindingRow_mem P p r hr)
  · let r := row (((List.range 3).map (fun i => (1,.binding p.val i false))) ++ [(-1,.parameter p.val)])
    have hr : r ∈ bindingRows p.val := by
      unfold CompilerScaffold.bindingRows
      simp only [List.mem_append]
      left; right
      exact List.mem_cons_self ..
    apply sub_eq_zero.mp
    calc
      _ = evalRow e F r := by norm_num [evalRow,row,r,List.range_succ,Fin.sum_univ_succ] <;> module
      _ = 0 := hrows r (bindingRow_mem P p r hr)

/-- Sharp frame pieces and their complementary pieces determine the parameter's
actual action on every qutrit frame projection. -/
theorem parameter_frame_action (e : Op) (F : ProjectionName → Op)
    (hp : ∀ n,Projection (F n))
    (hframe : ∀ i j : Fin 3,F (.frame i.val)*F (.frame j.val)=
      if i=j then F (.frame j.val) else 0)
    (p : ℕ)
    (hb : ∀ i : Fin 3,F (.binding p i.val false)+F (.binding p i.val true)=F (.frame i.val))
    (hs : (∑ i : Fin 3,F (.binding p i.val false))=F (.parameter p)) (i : Fin 3) :
    F (.parameter p)*F (.frame i.val)=F (.binding p i.val false) ∧
      F (.frame i.val)*F (.parameter p)=F (.binding p i.val false) := by
  have hpos (n : ProjectionName) : Positive (F n) :=
    ContinuousLinearMap.IsPositive.of_isStarProjection ⟨(hp n).2,(hp n).1⟩
  have hsupport (j : Fin 3) : F (.binding p j.val false)*F (.frame j.val)=F (.binding p j.val false) := by
    have hh := positive_below_projection (F (.binding p j.val false)) (F (.frame j.val))
      (hpos _) (hp _) (by rw [← hb j,add_sub_cancel_left]; exact hpos _)
    exact hh.1
  have hcross (j k : Fin 3) : F (.binding p j.val false)*F (.frame k.val)=
      if j=k then F (.binding p j.val false) else 0 := by
    calc
      _ = (F (.binding p j.val false)*F (.frame j.val))*F (.frame k.val) := by rw [hsupport j]
      _ = F (.binding p j.val false)*(F (.frame j.val)*F (.frame k.val)) := mul_assoc _ _ _
      _ = _ := by
        rw [hframe]
        split_ifs with hjk
        · subst k
          exact hsupport j
        · exact mul_zero _
  have ha : F (.parameter p)*F (.frame i.val)=F (.binding p i.val false) := by
    rw [← hs,Finset.sum_mul]
    simp_rw [hcross]
    simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  refine ⟨ha,?_⟩
  have hh := congrArg (fun A : Op => star A) ha
  simpa only [star_mul,(hp (.parameter p)).1,(hp (.frame i.val)).1,(hp (.binding p i.val false)).1] using hh

theorem actual_parameter_frame (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e)
    (hrows : ∀ r ∈ rowList P,evalRow e (projectionA P S e) r=0) (p : Fin 25) (i : Fin 3) :
    projectionA P S e (.parameter p.val)*projectionA P S e (.frame i.val)=
        projectionA P S e (.binding p.val i.val false) ∧
      projectionA P S e (.frame i.val)*projectionA P S e (.parameter p.val)=
        projectionA P S e (.binding p.val i.val false) := by
  have hb := binding_equations P e (projectionA P S e) hrows p
  exact parameter_frame_action e (projectionA P S e) (sharpA P S hS h hm e he)
    (actual_frame P S hS h hm e he hrows).2.1 p.val hb.1 hb.2 i

theorem parameter_frame_commutes (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e)
    (hrows : ∀ r ∈ rowList P,evalRow e (projectionA P S e) r=0) (p : Fin 25) (i : Fin 3) :
    Commute (projectionA P S e (.parameter p.val)) (projectionA P S e (.frame i.val)) := by
  have hh := actual_parameter_frame P S hS h hm e he hrows p i
  exact hh.1.trans hh.2.symm

#print axioms binding_equations
#print axioms parameter_frame_action
#print axioms actual_parameter_frame
#print axioms parameter_frame_commutes
end Sigma2.CompilerSoundnessParameters
