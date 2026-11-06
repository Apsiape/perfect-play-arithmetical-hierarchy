import Sigma2.CompilerSoundnessSupport
import Sigma2.FiniteSpectral

/-! Concrete FMS-to-dictionary bindings on the original state support.
The common opposite binary question fixes the local coarse projection. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace Sigma2.CompilerSoundnessBindings
open Compiler CompilerScaffold CompilerSoundnessNames Preliminaries TensorLifts CoarseCells
  FiniteSpectral MirrorAlgebra
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

theorem parameter_mem (P : Presentation) (i : ℕ) (hi : i<25) : .parameter i ∈ names P := by
  have hh : ProjectionName.parameter i ∈ (List.range 25).map ProjectionName.parameter :=
    List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  simp only [names,List.mem_dedup,List.mem_append]
  tauto

theorem active_mem (P : Presentation) (g : Fin 4) : .active g.val ∈ names P := by
  have hh : ProjectionName.active g.val ∈ (List.range 4).map ProjectionName.active :=
    List.mem_map.mpr ⟨g.val,List.mem_range.mpr g.isLt,rfl⟩
  simp only [names,List.mem_dedup,List.mem_append]
  tauto

theorem frame_mem (P : Presentation) (i : Fin 3) : .frame i.val ∈ names P := by
  have hh : ProjectionName.frame i.val ∈ (List.range 3).map ProjectionName.frame :=
    List.mem_map.mpr ⟨i.val,List.mem_range.mpr i.isLt,rfl⟩
  simp only [names,List.mem_dedup,List.mem_append]
  tauto

theorem pure_coarse_identify {s} (S : PureStrategy s) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (e : Op) (he : SupportOf h e)
    (x z : QA s) (y : QB s) (f u : ℕ → Bool)
    (hxy : ∀ a b,f a.val≠u b.val → S.probability x y a b=0)
    (hzy : ∀ a b,u a.val≠u b.val → S.probability z y a b=0) :
    coarse (compressed e (S.measurements.alice x)) (fun a => f a.val) true=
      coarse (compressed e (S.measurements.alice z)) (fun a => u a.val) true := by
  have han (w : QA s) (v : ℕ → Bool)
      (hz : ∀ a b,v a.val≠u b.val → S.probability w y a b=0) :=
    coarse_analysis S h hm e he
      (S.measurements.alice w) (S.measurements.bob y)
      (S.measurements.alice_pos _) (S.measurements.bob_pos _)
      (S.measurements.alice_sum _) (S.measurements.bob_sum _)
      (fun a => v a.val) (fun b => u b.val)
      (fun a b hab => by simpa only [PureStrategy.probability,measurements_left,measurements_right] using hz a b hab) true
  have hx := han x f hxy
  have hz := han z u hzy
  rw [coarse_compressed,coarse_compressed]
  apply local_eq S h hm e he _ _ (by simp [mul_assoc,he.1.2]) (by simp [mul_assoc,he.1.2])
  have hs := left_support S h hm e he
  have h1 := compressed_mirror S.vector e 1 _ _ hs (by simp [right_one]) hx.1
  have h2 := compressed_mirror S.vector e 1 _ _ hs (by simp [right_one]) hz.1
  exact h1.trans h2.symm

theorem coarse_identify {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalA S h) (e : Op) (he : SupportOf h e)
    (x z : QA s) (y : QB s) (f u : ℕ → Bool)
    (hxy : ∀ a b,f a.val≠u b.val → S.probability x y a b=0)
    (hzy : ∀ a b,u a.val≠u b.val → S.probability z y a b=0) :
    coarse (compressed e (S.measurements.alice x)) (fun a => f a.val) true=
      coarse (compressed e (S.measurements.alice z)) (fun a => u a.val) true := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  have hh := pure_coarse_identify T h (hM h hm) e he x z y f u
    (fun a b hab => (hprob x y a b).symm.trans (hxy a b hab))
    (fun a b hab => (hprob z y a b).symm.trans (hzy a b hab))
  simpa only [hA] using hh

theorem coarse_single (E : Fin 12 → Op) (a : Fin 12) :
    coarse E (fun b => decide (b.val=a.val)) true=E a := by
  have ht (b : Fin 12) : decide (b.val=a.val)=true ↔ b=a := by simp [Fin.ext_iff]
  simp only [coarse,ht,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem bind_alice (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (x : QA (scenario P))
    (n : ProjectionName) (hn : n ∈ names P) (f : ℕ → Bool)
    (hbind : ∀ a b,f a.val≠decide (b.val=1) →
      S.probability x (namedEvent P n hn).y a b=0) :
    coarse (compressed e (S.measurements.alice x)) (fun a => f a.val) true=
      projectionA P S e n := by
  have hsync := synchronized P S hS (nameIndex P n hn)
  have hh := coarse_identify S h hm e he x (namedEvent P n hn).x (namedEvent P n hn).y
    f (fun b => decide (b=1)) hbind (fun a b hab => by
      apply hsync a b
      intro heq
      apply hab
      have hv : a.val=1 ↔ b.val=1 := by simpa only [namedEvent,event,Fin.ext_iff] using heq
      by_cases ha : a.val=1
      · have hb := hv.mp ha
        simp only [ha,hb,decide_true]
      · have hb : b.val≠1 := fun hh => ha (hv.mpr hh)
        simp only [ha,hb,decide_false])
  rw [projectionA_of_mem P S e n hn]
  exact hh.trans (coarse_single (compressed e (S.measurements.alice (namedEvent P n hn).x)) 1)

theorem rule_true_directed (P : Presentation) (q p : Question) (a b : ℕ)
    (hr : rule P q p a b=true) : directed P true q p a b=true := by
  simp only [rule,Bool.and_eq_true] at hr
  exact hr.1.2

theorem fms_binding (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (g : Fin 4) (x : Fin 5)
    (n : ProjectionName) (hn : n ∈ names P) (f : ℕ → Bool)
    (hb : ∀ a b,fmsBinding true g.val x.val n a b=true → (f a=true ↔ b=1)) :
    coarse (compressed e (S.measurements.alice ((fmsInstance P g).qA x))) (fun a => f a.val) true=
      projectionA P S e n := by
  apply bind_alice P S hS h hm e he _ n hn f
  intro a b hab
  apply pre_rejected_probability P S hS
  apply Bool.eq_false_iff.mpr
  intro hr
  have hd := rule_true_directed P _ _ a.val b.val hr
  change directed P true (question P ((names P).length+5*g.val+x.val))
    (question P (namedEvent P n hn).x.val) a.val b.val=true at hd
  rw [question_fms,question_named] at hd
  change fmsBinding true g.val x.val n a.val b.val=true at hd
  have hv := hb a.val b.val hd
  apply hab
  cases hf : f a.val <;> cases hh : decide (b.val=1) <;> simp_all

/-- The named active projection is the actual coarse active event. -/
theorem active_binding (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (g : Fin 4) (x : Fin 5) :
    coarse (compressed e (S.measurements.alice ((fmsInstance P g).qA x)))
      (fun a => decide (a.val<5)) true=projectionA P S e (.active g.val) := by
  apply fms_binding P S hS h hm e he g x _ (active_mem P g) (fun a => decide (a<5))
  intro a b hb
  simp only [fmsBinding,Bool.and_eq_true] at hb
  simpa only [ite_true,decide_eq_true_eq] using hb.1.1.1

/-- The concrete named source parameter is the actual original flag. -/
theorem flag_binding (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (g : Fin 4) :
    e*flagA S (fmsInstance P g)*e=projectionA P S e (.parameter (cornerIndex g.val)) := by
  have hn : ProjectionName.parameter (cornerIndex g.val) ∈ names P :=
    parameter_mem P _ (by have := g.isLt; unfold cornerIndex; split_ifs <;> omega)
  have hh := fms_binding P S hS h hm e he g 0 _ hn (fun a => decide (a=0)) (by
    intro a b hb
    simp only [fmsBinding,Bool.and_eq_true] at hb
    simpa only [Fin.val_zero,show (0:ℕ)<3 by decide,true_and,ite_true,decide_eq_true_eq] using hb.1.1.2)
  exact (coarse_single (compressed e (S.measurements.alice ((fmsInstance P g).qA 0))) 0).symm.trans hh

theorem magic_coarse_binding (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (g k : Fin 4) (x : Fin 5)
    (hx : x.val=if k.val=0 then 4 else 3) :
    coarse (compressed e (S.measurements.alice ((fmsInstance P g).qA x)))
      (fun a => decide (a.val=(if k.val=0 then 2 else k.val+1))) true=
        projectionA P S e (.parameter (1+4*g.val+k.val)) := by
  have hn := parameter_mem P (1+4*g.val+k.val) (by have := g.isLt; have := k.isLt; omega)
  apply fms_binding P S hS h hm e he g x _ hn
    (fun a => decide (a=(if k.val=0 then 2 else k.val+1)))
  intro a b hb
  simp only [fmsBinding,Bool.and_eq_true] at hb
  have hh := List.all_eq_true.mp hb.1.2 k.val (List.mem_range.mpr k.isLt)
  simpa only [ite_true,Bool.true_eq,hx,decide_eq_true_eq] using hh

theorem magic_binding (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (g k : Fin 4) :
    e*magicA S (fmsInstance P g) k*e=
      projectionA P S e (.parameter (1+4*g.val+k.val)) := by
  fin_cases k
  · have hh := magic_coarse_binding P S hS h hm e he g 0 4 (by decide)
    exact (coarse_single (compressed e (S.measurements.alice ((fmsInstance P g).qA 4))) 2).symm.trans hh
  · have hh := magic_coarse_binding P S hS h hm e he g 1 3 (by decide)
    exact (coarse_single (compressed e (S.measurements.alice ((fmsInstance P g).qA 3))) 2).symm.trans hh
  · have hh := magic_coarse_binding P S hS h hm e he g 2 3 (by decide)
    exact (coarse_single (compressed e (S.measurements.alice ((fmsInstance P g).qA 3))) 3).symm.trans hh
  · have hh := magic_coarse_binding P S hS h hm e he g 3 3 (by decide)
    exact (coarse_single (compressed e (S.measurements.alice ((fmsInstance P g).qA 3))) 4).symm.trans hh

theorem axis_binding (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (g : Fin 4) (k : Fin 2) (x : Fin 5)
    (hx : x.val=if k.val=0 then 1 else 0) :
    coarse (compressed e (S.measurements.alice ((fmsInstance P g).qA x)))
      (fun a => decide (0<a.val ∧ a.val<5 ∧ cellSign false (a.val-1) 1=false)) true=
        projectionA P S e (.parameter (17+2*g.val+k.val)) := by
  have hn := parameter_mem P (17+2*g.val+k.val) (by have := g.isLt; have := k.isLt; omega)
  apply fms_binding P S hS h hm e he g x _ hn
    (fun a => decide (0<a ∧ a<5 ∧ cellSign false (a-1) 1=false))
  intro a b hb
  simp only [fmsBinding,Bool.and_eq_true] at hb
  have hh := List.all_eq_true.mp hb.2 k.val (List.mem_range.mpr k.isLt)
  simpa only [ite_true,Bool.true_eq,hx,decide_eq_true_eq] using hh

#print axioms parameter_mem
#print axioms active_mem
#print axioms frame_mem
#print axioms coarse_identify
#print axioms bind_alice
#print axioms fms_binding
#print axioms active_binding
#print axioms flag_binding
#print axioms magic_binding
#print axioms axis_binding
end Sigma2.CompilerSoundnessBindings
