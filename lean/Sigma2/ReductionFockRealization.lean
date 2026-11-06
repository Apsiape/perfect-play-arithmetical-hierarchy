import Sigma2.ReductionFockLabels
import Sigma2.ReductionEval

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 400000
set_option pp.proofs false
set_option backward.isDefEq.respectTransparency true
namespace Sigma2.ReductionFockModel
open Sigma2.Tree Sigma2.Reduction Sigma2.Reduction.Syntax
variable (q : ℕ) [NeZero q] (M : Automaton) (ζ : ℂ) (hnorm : ‖ζ‖=1)
  (hprim : IsPrimitiveRoot ζ q)
  (hsep : ∀ y, 0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖)
  (hn : ∀ t x,run M (classicalPulse q) t x≠2)
attribute [local irreducible] Sigma2.Reduction.Syntax.sum List.ofFn
attribute [local irreducible] Sigma2.ReductionFockModel.root Sigma2.ReductionFockModel.ux Sigma2.ReductionFockModel.uy Sigma2.ReductionFockModel.px Sigma2.ReductionFockModel.py Sigma2.ReductionFockModel.wave Sigma2.ReductionFockModel.counter Sigma2.ReductionFockModel.phaseOp Sigma2.ReductionFockModel.jOp Sigma2.ReductionFockModel.kOp Sigma2.ReductionFockModel.pulse Sigma2.ReductionFockModel.inverseReader Sigma2.ReductionFockModel.creation Sigma2.ReductionFockModel.symbol
local notation "V" => label q M ζ hnorm hsep

include hprim hn

theorem fixed_equations (p : Expr) (hp : p∈[sub (.mul (L 1) (L 0)) (L 0),sub (.mul (L 2) (L 0)) (L 0),
       sub (.mul (L 3) (L 0)) (L 0),sub (.mul (L 4) (L 0)) (L 0),
       sub (.mul (L 5) (L 0)) (L 0),sub (.mul (L 6) (L 0)) (L 0),
       sub (.mul (L 8) (L 9)) (mul3 (L 7) (L 9) (L 8)),
       .mul (sub (L 5) I) (L 10),
       sub (.mul (L 11) (sub (L 5) I)) (.mul (.scalar (1/2)) (.mul (L 6) (sub I (L 10)))),
       sub (mul3 (sym 0) (L 3) (L 4)) (.mul (L 3) (L 4)),
       sub (mul3 (sym 1) (sub I (L 3)) (L 4)) (.mul (sub I (L 3)) (L 4)),
       sym 2,sub (sum ((List.ofFn (fun c : Symbol M => c)).map (fun c => sym c.val))) I]) : p.eval 1 V=0 := by
  have h0 : 0<M.extraSymbols+3 := by omega
  have h1 : 1<M.extraSymbols+3 := by omega
  have h2 : 2<M.extraSymbols+3 := by omega
  have hs2 : (⟨2,h2⟩ : Symbol M)=2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt h2]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (ux_root q)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (uy_root q)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (px_root q)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (py_root q)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (wave_root q ζ hnorm)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (counter_root q)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (weyl q ζ hprim hnorm)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using return_row q ζ hprim hnorm
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (reader_row q ζ hprim hnorm hsep)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (initial_start q M)
  · simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (initial_blank q M)
  · simpa [label,Expr.eval,h0,h1,h2,hs2,smul_mul_assoc] using symbol_no_halt q M hn
  · simpa only [ReductionEval.eval_sub,ReductionEval.eval_sum,List.map_map,
      List.map_ofFn,List.sum_ofFn,Function.comp_def,ReductionEval.eval_sym,label_symbol,
      ReductionEval.eval_I] using sub_eq_zero.mpr (symbol_partition q M)

theorem central_equations (p : Expr) (hp : p∈(applicationPresentation M).central) : p.eval 1 V=0 := by
  dsimp only [applicationPresentation] at hp
  simp only [List.mem_append] at hp
  rcases hp with (hf | hc) | ht
  · exact fixed_equations q M ζ hnorm hprim hsep hn p hf
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    simpa [Syntax.comm,label,Expr.eval] using sub_eq_zero.mpr (phase_commutes q ζ (V i))
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    rw [ReductionEval.eval_transition]
    simp only [label_symbol]
    simp only [label]
    have h := transition_row q M a
    simp only [ReductionFockModel.leftFactor,ReductionFockModel.rightFactor,
      ReductionFockModel.lastX,ReductionFockModel.lastY,event] at h
    convert h using 1

omit hprim hn

theorem endpoint_equations (r : Expr × Fin 4 × Fin 4 × Expr)
    (hr : r∈(applicationPresentation M).endpoints) :
    r.1.eval 1 V*creation q r.2.1=creation q r.2.2.1*r.2.2.2.eval 1 V := by
  dsimp only [applicationPresentation] at hr
  simp only [List.mem_append] at hr
  rcases hr with (hx | hy) | hc
  · obtain ⟨b,hb,hr⟩ := List.mem_flatMap.mp hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa [Expr.eval,L,I,label] using (ux_rec q b).1
    · simpa [Expr.eval,L,I,label] using (ux_rec q b).2
    · simpa [Expr.eval,L,I,label] using (px_rec q b).1
  · obtain ⟨a,ha,hr⟩ := List.mem_flatMap.mp hy
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · simpa [Expr.eval,L,I,label] using (uy_rec q a).1
    · simpa [Expr.eval,L,I,label] using (uy_rec q a).2
    · simpa [Expr.eval,L,I,label] using (py_rec q a).1
  · obtain ⟨a,ha,hr⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simpa [Expr.eval,L,I,label,apply_ite] using wave_rec q ζ hnorm a
    · by_cases h : a.val%2=0 <;>
        simpa [Expr.eval,L,I,label,h,smul_mul_assoc] using counter_rec q a
    · simpa [Expr.eval,L,I,label] using phase_rec q ζ a
    · simpa [Expr.eval,L,I,label] using j_rec q a
    · simpa [Expr.eval,L,I,label] using k_rec q ζ hnorm a

theorem zero_equations (r : Expr × Fin 4) (hr : r∈(applicationPresentation M).zeros) :
    r.1.eval 1 V*creation q r.2=0 := by
  dsimp only [applicationPresentation] at hr
  simp only [List.mem_append] at hr
  rcases hr with hx | hy
  · obtain ⟨b,hb⟩ := List.mem_ofFn.mp hx
    subst r
    simpa [Expr.eval,L,label] using (px_rec q b).2
  · obtain ⟨a,ha⟩ := List.mem_ofFn.mp hy
    subst r
    simpa [Expr.eval,L,label] using (py_rec q a).2

/-- All fields of the frozen presentation are realized on the concrete Fock basis. -/
def realization : NormalRealization (applicationPresentation M) where
  support := 1
  support_projection := by simp [Projection]
  density := density q
  density_supported := one_mul _
  faithful_on := by
    intro v hv hz
    exact density_faithful q (hz.trans (map_zero _).symm)
  label := V
  creation := creation q
  label_supported := fun i => ⟨one_mul _,mul_one _⟩
  creation_supported := fun a => ⟨one_mul _,mul_one _⟩
  typed := by
    intro i
    exact label_typed q M ζ hnorm hsep i.val (by
      simpa only [types_length M] using i.isLt)
  centralizer := label_centralizer q M ζ hnorm hsep
  isometries := creation_isometries q
  ranges := by simpa only [applicationPresentation,buildPresentation,label,support] using creation_ranges q
  modular := modular q
  central_equations := central_equations q M ζ hnorm hprim hsep hn
  endpoint_equations := endpoint_equations q M ζ hnorm hsep
  zero_equations := zero_equations q M ζ hnorm hsep
  linear_equations := by simp [applicationPresentation,buildPresentation]

include hprim hn

lemma realization_finiteEntropy :
    RealizationFiniteEntropy (realization q M ζ hnorm hprim hsep hn) := density_finiteEntropy q

#print axioms realization
#print axioms realization_finiteEntropy
end Sigma2.ReductionFockModel
