import Sigma2.CompilerHonestCoarseLift
import Sigma2.CompilerHonestBindingAlgebra

/-! An orientation-uniform bridge from coarse identities to the actual frozen
 binary FMS binding predicate. -/
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestBindings
open Compiler CompilerScaffold CompilerHonestCoarseLift CompilerProjectionDictionary
  CompilerHonestCentralizer CompilerHonestState CompilerHonestRefinementCommute
  CompilerHonestFMSLift CompilerHonestAxisMirrors CompilerHonestAxes
  CompilerHonestScalar CompilerHonestCoarse CoefficientOperator RowCompleteness TensorLifts
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials CompilerScaffold.structuralPolynomials
  CompilerScaffold.applicationPolynomials

def answer (b : Bool) : ℕ := if b then 1 else 0
@[simp] theorem answer_one (b : Bool) : answer b=1 ↔ b=true := by cases b <;> simp [answer]

def bindingVector {P : Presentation} (R : StructuralRealization P)
    (bob : Bool) (g : Fin 4) (x : Fin 5) (n : ProjectionName) (a : Fin 6) (b : Bool) : AB :=
  if bob then
    (left ((Partition.binary (projection R n) (projection_projective R n).1
      (projection_projective R n).2).effect b)*right ((fms true g x).effect a))
      (vector (density R.density))
  else
    (left ((fms false g x).effect a)*right ((Partition.binary (transpose (projection R n))
      (transpose_projection _ (projection_projective R n)).1
      (transpose_projection _ (projection_projective R n)).2).effect b))
      (vector (density R.density))

theorem consistent {P : Presentation} (R : StructuralRealization P)
    (bob : Bool) (g : Fin 4) (x : Fin 5) (n : ProjectionName) (a : Fin 6) (b : Bool)
    (f : Fin 6 → Bool)
    (he : ((fms bob g x).coarse f).effect true=
      if bob then transpose (projection R n) else projection R n)
    (hne : bindingVector R bob g x n a b≠0) : f a=b := by
  by_contra h
  cases bob
  · exact hne (CompilerHonestBindingAlgebra.alice_zero _ f _ _
      (projection_projective R n) (transpose_projection _ (projection_projective R n))
      he _ (mirror _ _ (projection_centralizer R n)) a b h)
  · exact hne (CompilerHonestBindingAlgebra.bob_zero _ f _ _
      (projection_projective R n) (transpose_projection _ (projection_projective R n))
      he _ (mirror _ _ (projection_centralizer R n)) b a h)

theorem coarse_single (Q : Partition Op (Fin 6)) (a : Fin 6) :
    (Q.coarse (fun b => decide (b=a))).effect true=Q.effect a := by
  apply Partition.coarse_single _ _ true a
  intro b
  simp

theorem activity_transpose {P : Presentation} (R : StructuralRealization P) (g : Fin 4) :
    transpose (projection R (.active g.val))=projection R (.active g.val) := by
  change transpose (FiniteAncilla.amplify 3 (CompilerFiniteRegister.mask 17 _))=
    FiniteAncilla.amplify 3 (CompilerFiniteRegister.mask 17 _)
  rw [transpose_amplify,← scalar_active,transpose_scalar,active_diagonal]
  congr 2
  ext i j
  by_cases h : i=j <;> simp [Matrix.transpose_apply,Matrix.diagonal_apply,h,Ne.symm]

theorem parameter_transpose' {P : Presentation} (R : StructuralRealization P) (i : Fin 17) :
    transpose (projection R (.parameter i.val))=projection R (.parameter i.val) := by
  change transpose (FiniteAncilla.amplify 3 (CompilerHonestDictionary.parameter i.val))=
    FiniteAncilla.amplify 3 (CompilerHonestDictionary.parameter i.val)
  rw [transpose_amplify,parameter_transpose]

/-- A nonzero actual FMS/binary event satisfies every retained directed
 activity, flag, chosen-magic, and positive-axis check. -/
theorem binding_accepts {P : Presentation} (R : StructuralRealization P)
    (bob : Bool) (g : Fin 4) (x : Fin 5) (n : ProjectionName) (a : Fin 6) (b : Bool)
    (hne : bindingVector R bob g x n a b≠0) :
    fmsBinding (!bob) g.val x.val n a.val (answer b)=true := by
  simp only [fmsBinding,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · split_ifs with hn
    · subst n
      have he : ((fms bob g x).coarse (fun a => decide (a.val<5))).effect true=
          if bob then transpose (projection R (.active g.val)) else projection R (.active g.val) := by
        change (∑ a : Fin 6,if decide (a.val<5)=true then _ else 0)=_
        simp only [decide_eq_true_eq]
        rw [activity_binding R]
        cases bob <;> simp [activity_transpose]
      have h := consistent R bob g x _ a b _ he hne
      simpa only [decide_eq_true_eq,answer_one,← h,Bool.decide_iff,decide_true] using
        (show decide ((a.val<5) ↔ b=true)=true by rw [← h]; simp)
    · rfl
  · split_ifs with hh
    · rcases hh with ⟨hx,hn⟩
      subst n
      have he : ((fms bob g x).coarse (fun a => decide (a=0))).effect true=
          if bob then transpose (projection R (.parameter (cornerIndex g.val)))
            else projection R (.parameter (cornerIndex g.val)) := by
        rw [coarse_single]
        have hf := flag_binding R bob g ⟨x.val,hx⟩
        have hg := g.isLt
        have hn : cornerIndex g.val<17 := by unfold cornerIndex; split_ifs <;> omega
        simpa only [Fin.eta,parameter_transpose' R ⟨cornerIndex g.val,hn⟩,ite_self] using hf
      have h : decide (a=0)=b := consistent R bob g x _ a b _ he hne
      simp only [decide_eq_true_eq,answer_one]
      rw [← h]
      simp only [decide_eq_true_eq,Fin.ext_iff,Fin.val_zero]
    · rfl
  · intro k hk
    have hk4 : k<4 := List.mem_range.mp hk
    by_cases hn : n=.parameter (1+4*g.val+k)
    · rw [if_pos hn]
      subst n
      cases hb : bob
      · simp only [Bool.not_false,Bool.true_eq,ite_true]
        by_cases hx : x.val=(if k=0 then 4 else 3)
        · rw [if_pos hx]
          have hxe : x=(if (⟨k,hk4⟩ : Fin 4)=0 then 4 else 3) := by
            apply Fin.ext
            interval_cases k <;> simpa using hx
          have he : ((fms false g x).coarse (fun a => decide
              (a=(⟨if k=0 then 2 else k+1,by split_ifs <;> omega⟩ : Fin 6)))).effect true=
              projection R (.parameter (1+4*g.val+k)) := by
            rw [coarse_single,hxe]
            change (CompilerHonestFMSLift.alice g _).effect _=_
            simpa only [Fin.ext_iff,Fin.val_zero,Fin.val_mk] using alice_magic_binding R g ⟨k,hk4⟩
          have h := consistent R false g x _ a b _ he (by simpa only [hb] using hne)
          simp only [decide_eq_true_eq,answer_one]
          rw [← h]
          simp only [decide_eq_true_eq,Fin.ext_iff,Fin.val_mk]
        · rw [if_neg hx]
      · simp only [Bool.not_true,Bool.false_eq_true,ite_false]
        by_cases hx : x.val=0
        · rw [if_pos hx]
          have hxe : x=0 := Fin.ext hx
          have hn17 : 1+4*g.val+k<17 := by have := g.isLt; omega
          have he : ((fms true g x).coarse (fun a => decide
              (a=(⟨k+1,by omega⟩ : Fin 6)))).effect true=
              transpose (projection R (.parameter (1+4*g.val+k))) := by
            rw [coarse_single,hxe,parameter_transpose' R ⟨1+4*g.val+k,hn17⟩]
            change (CompilerHonestFMSLift.bob g _).effect _=_
            exact bob_magic_binding R g ⟨k,hk4⟩
          have h := consistent R true g x _ a b _ he (by simpa only [hb] using hne)
          simp only [decide_eq_true_eq,answer_one]
          rw [← h]
          simp only [decide_eq_true_eq,Fin.ext_iff,Fin.val_mk]
        · rw [if_neg hx]
    · rw [if_neg hn]
  · intro k hk
    have hk2 : k<2 := List.mem_range.mp hk
    by_cases hn : n=.parameter (17+2*g.val+k)
    · rw [if_pos hn]
      subst n
      cases hb : bob
      · simp only [Bool.not_false,Bool.true_eq,ite_true]
        by_cases hx : x.val=(if k=0 then 1 else 0)
        · rw [if_pos hx]
          have hxe : x=(if (⟨k,hk2⟩ : Fin 2)=0 then 1 else 0) := by
            apply Fin.ext
            interval_cases k <;> simpa using hx
          have he : ((fms false g x).coarse (fun a => decide
              (0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false))).effect true=
              projection R (.parameter (17+2*g.val+k)) := by
            change (∑ a : Fin 6,if decide (0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false)=true then (fms false g x).effect a else 0)=_
            simp only [decide_eq_true_eq]
            rw [hxe]
            change (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false then
              (CompilerHonestFMSLift.alice g (if (⟨k,hk2⟩ : Fin 2)=0 then 1 else 0)).effect a else 0)=_
            simpa only [Fin.ext_iff,Fin.val_zero,Fin.val_mk,CompilerProjectionDictionary.projection] using alice_axis_binding g ⟨k,hk2⟩
          have h := consistent R false g x _ a b _ he (by simpa only [hb] using hne)
          simp only [decide_eq_true_eq,answer_one]
          rw [← h]
          simp only [decide_eq_true_eq,iff_self]
        · rw [if_neg hx]
      · simp only [Bool.not_true,Bool.false_eq_true,ite_false]
        by_cases hx : x.val=1
        · rw [if_pos hx]
          have hxe : x=1 := Fin.ext hx
          have he : ((fms true g x).coarse (fun a => decide
              (0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) (if k=0 then 1 else 0)=false))).effect true=
              transpose (projection R (.parameter (17+2*g.val+k))) := by
            change (∑ a : Fin 6,if decide (0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) (if k=0 then 1 else 0)=false)=true then (fms true g x).effect a else 0)=_
            simp only [decide_eq_true_eq]
            rw [hxe]
            rw [CompilerProjectionDictionary.projection,transpose_amplify,axis_transpose g ⟨k,hk2⟩]
            change (∑ a : Fin 6,if 0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) (if k=0 then 1 else 0)=false then
              (CompilerHonestFMSLift.bob g 1).effect a else 0)=_
            simpa only [Fin.ext_iff,Fin.val_zero,Fin.val_mk] using bob_axis_binding g ⟨k,hk2⟩
          have h := consistent R true g x _ a b _ he (by simpa only [hb] using hne)
          simp only [decide_eq_true_eq,answer_one]
          rw [← h]
          simp only [decide_eq_true_eq,iff_self]
        · rw [if_neg hx]
    · rw [if_neg hn]

#print axioms binding_accepts
end Sigma2.CompilerHonestBindings
