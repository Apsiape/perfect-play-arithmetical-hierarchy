import Sigma2.FockTruncationEquations
import Sigma2.FockTruncationEstimates

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 400000
namespace Sigma2.FockTruncation
open Sigma2.Tree Sigma2.Reduction Sigma2.ReductionFockModel
variable (q : ℕ) [NeZero q] (M : Automaton) (ζ : ℂ) (hnorm : ‖ζ‖=1)
  (hsep : ∀ y,0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖)
local notation "V" => label q M ζ hnorm hsep

lemma endpoint_equations_cut (m : ℕ) (r : Expr × Fin 4 × Fin 4 × Expr)
    (hr : r ∈ (applicationPresentation M).endpoints) :
    r.1.eval (cut q m) (fun i => cut q m * V i) * creation q m r.2.1 =
      creation q m r.2.2.1 * r.2.2.2.eval (cut q m) (fun i => cut q m * V i) := by
  rw [CornerCompression.eval _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep),
    CornerCompression.eval _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep)]
  rw [creation,CornerCompression.mul _ (cut_projection q m) _ _
    (CornerCompression.commute_eval _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep) r.1)]
  rw [ReductionFockModel.endpoint_equations q M ζ hnorm hsep r hr]
  rw [← mul_assoc]
  exact congrArg (fun T : Op => T*r.2.2.2.eval 1 V) (creation_supported q m r.2.2.1).2.symm

lemma zero_equations_cut (m : ℕ) (r : Expr × Fin 4)
    (hr : r ∈ (applicationPresentation M).zeros) :
    r.1.eval (cut q m) (fun i => cut q m * V i) * creation q m r.2 = 0 := by
  rw [CornerCompression.eval _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep),
    creation,CornerCompression.mul _ (cut_projection q m) _ _
      (CornerCompression.commute_eval _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep) r.1),
    ReductionFockModel.zero_equations q M ζ hnorm hsep r hr,mul_zero]

lemma symbol_no_halt_cut (m : ℕ) (hm : 2^m ≤ q)
    (hsafe : ∀ t x,t ≤ q → run M (classicalPulse q) t x ≠ 2) :
    cut q m * symbol q M 2 = 0 := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  by_cases hl : w.length ≤ m
  · have htime : yCoord w ≤ q := by
      have hb := (coord_bounds w).2
      have hp : 2^w.length ≤ 2^m := Nat.pow_le_pow_right (by omega) hl
      omega
    have hh := hsafe (yCoord w) (xCoord w) htime
    simp [mul_apply_eq_comp,symbol_basis,hh]
  · simp [mul_apply_eq_comp,symbol_basis,apply_ite,hl]

lemma sum_map_zero {α : Type} (l : List α) (f : α → ℝ) (h : ∀ a ∈ l,f a=0) :
    (l.map f).sum=0 := by
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
  exact h a ha

lemma sum_map_flatMap {α β : Type} (l : List α) (g : α → List β) (f : β → ℝ) :
    ((l.flatMap g).map f).sum = (l.map (fun a => ((g a).map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

lemma residual_sum (m : ℕ) (hprim : IsPrimitiveRoot ζ q)
    (hz : cut q m * symbol q M 2=0) :
    ((Compiler.applicationResiduals (applicationPresentation M) (structural q m M ζ hnorm hsep)).map
      (fun r => (trace ((density q m).op * (star r*r))).re)).sum =
      4*(3 / ((4:ℝ)^(m+1)-1)) := by
  let E := cut q m
  let L := fun i => E * V i
  let D := creation q m
  let f := fun r : Op => (trace ((density q m).op*(star r*r))).re
  have hf : f 0=0 := by simp [f,trace,entry]
  have hc : ((applicationPresentation M).central.map (fun p => f (p.eval E L))).sum=0 := by
    apply sum_map_zero
    intro p hp
    rw [central_equations_cut q M ζ hnorm hprim hsep m hz p hp]
    exact hf
  have he : ((applicationPresentation M).endpoints.map (fun r =>
      f (r.1.eval E L*D r.2.1-D r.2.2.1*r.2.2.2.eval E L))).sum=0 := by
    apply sum_map_zero
    intro r hr
    rw [endpoint_equations_cut q M ζ hnorm hsep m r hr,sub_self]
    exact hf
  have hz' : ((applicationPresentation M).zeros.map (fun r => f (r.1.eval E L*D r.2))).sum=0 := by
    apply sum_map_zero
    intro r hr
    rw [zero_equations_cut q M ζ hnorm hsep m r hr]
    exact hf
  have hr : f ((∑ a,D a*star (D a))-(E-L (applicationPresentation M).root))=0 := by
    change f ((∑ a,creation q m a*star (creation q m a))-
      (cut q m-cut q m*root q))=0
    rw [ranges,cut_root,sub_self]
    exact hf
  have hi (a b : Fin 4) : f (star (D a)*D b-(if a=b then E else 0)) =
      if a=b then 3/((4:ℝ)^(m+1)-1) else 0 := by
    by_cases h : a=b
    · subst b
      simpa only [f,D,E,if_pos rfl,ite_true] using defect_trace q m a
    · change f (star (creation q m a)*creation q m b-(if a=b then cut q m else 0))=_
      rw [isometries,if_neg h,if_neg h,sub_self,if_neg h]
      exact hf
  change ((Compiler.applicationResiduals (applicationPresentation M)
    (structural q m M ζ hnorm hsep)).map f).sum=_
  simp only [Compiler.applicationResiduals,structural,List.map_append,List.sum_append,List.map_map,
    Function.comp_def]
  have hlinear : (applicationPresentation M).linear=[] := rfl
  simp only [hlinear,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  change _ + f ((∑ a,D a*star (D a))-(E-L (applicationPresentation M).root)) +
    ((applicationPresentation M).central.map (fun p => f (p.eval E L))).sum +
    ((applicationPresentation M).endpoints.map (fun r => f (r.1.eval E L*D r.2.1-D r.2.2.1*r.2.2.2.eval E L))).sum +
    ((applicationPresentation M).zeros.map (fun r => f (r.1.eval E L*D r.2))).sum = _
  rw [hc,he,hz',hr]
  simp only [add_zero]
  rw [sum_map_flatMap]
  simp only [List.map_ofFn,List.sum_ofFn]
  change (∑ a : Fin 4, ∑ b : Fin 4, f (star (D a)*D b-(if a=b then E else 0))) = _
  simp_rw [hi]
  simp

#print axioms residual_sum

end Sigma2.FockTruncation
