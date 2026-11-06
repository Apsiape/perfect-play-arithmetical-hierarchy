import Sigma2.FockTruncationStructural

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 400000
namespace Sigma2.FockTruncation
open Sigma2.Tree Sigma2.Reduction Sigma2.Reduction.Syntax Sigma2.ReductionFockModel
variable (q : ℕ) [NeZero q] (M : Automaton) (ζ : ℂ) (hnorm : ‖ζ‖=1)
  (hprim : IsPrimitiveRoot ζ q)
  (hsep : ∀ y,0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖)
local notation "V" => label q M ζ hnorm hsep
include hprim

theorem fixed_equations_cut (m : ℕ) (hz : cut q m * symbol q M 2 = 0) (p : Expr) (hp : p∈[sub (.mul (L 1) (L 0)) (L 0),sub (.mul (L 2) (L 0)) (L 0),
       sub (.mul (L 3) (L 0)) (L 0),sub (.mul (L 4) (L 0)) (L 0),
       sub (.mul (L 5) (L 0)) (L 0),sub (.mul (L 6) (L 0)) (L 0),
       sub (.mul (L 8) (L 9)) (mul3 (L 7) (L 9) (L 8)),
       .mul (sub (L 5) I) (L 10),
       sub (.mul (L 11) (sub (L 5) I)) (.mul (.scalar (1/2)) (.mul (L 6) (sub I (L 10)))),
       sub (mul3 (sym 0) (L 3) (L 4)) (.mul (L 3) (L 4)),
       sub (mul3 (sym 1) (sub I (L 3)) (L 4)) (.mul (sub I (L 3)) (L 4)),
       sym 2,sub (sum ((List.ofFn (fun c : Symbol M => c)).map (fun c => sym c.val))) I]) : p.eval (cut q m) (fun i => cut q m * V i)=0 := by
  rw [CornerCompression.eval _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep)]
  have h0 : 0<M.extraSymbols+3 := by omega
  have h1 : 1<M.extraSymbols+3 := by omega
  have h2 : 2<M.extraSymbols+3 := by omega
  have hs2 : (⟨2,h2⟩ : Symbol M)=2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt h2]
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (ux_root q)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (uy_root q)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (px_root q)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (py_root q)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (wave_root q ζ hnorm)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (counter_root q)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (weyl q ζ hprim hnorm)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using return_row q ζ hprim hnorm
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (reader_row q ζ hprim hnorm hsep)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (initial_start q M)
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [label,Expr.eval,h0,h1,h2,smul_mul_assoc] using sub_eq_zero.mpr (initial_blank q M)
  · simpa [label,Expr.eval,h0,h1,h2,hs2,smul_mul_assoc] using hz
  · apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa only [ReductionEval.eval_sub,ReductionEval.eval_sum,List.map_map,
        List.map_ofFn,List.sum_ofFn,Function.comp_def,ReductionEval.eval_sym,label_symbol,
        ReductionEval.eval_I] using sub_eq_zero.mpr (symbol_partition q M)
    
theorem central_equations_cut (m : ℕ) (hz : cut q m * symbol q M 2 = 0) (p : Expr) (hp : p∈(applicationPresentation M).central) : p.eval (cut q m) (fun i => cut q m * V i)=0 := by
  dsimp only [applicationPresentation] at hp
  simp only [List.mem_append] at hp
  rcases hp with (hf | hc) | ht
  · exact fixed_equations_cut q M ζ hnorm hprim hsep m hz p hf
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hc
    rw [CornerCompression.eval _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep)]
    apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    simpa [Syntax.comm,label,Expr.eval] using sub_eq_zero.mpr (phase_commutes q ζ (V i))
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp ht
    rw [CornerCompression.eval _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep)]
    apply (show ∀ A : Op, A=0 → cut q m * A=0 from fun A h => by rw [h,mul_zero])
    rw [ReductionEval.eval_transition]
    simp only [label_symbol]
    simp only [label]
    have h := transition_row q M a
    simp only [ReductionFockModel.leftFactor,ReductionFockModel.rightFactor,
      ReductionFockModel.lastX,ReductionFockModel.lastY,event] at h
    convert h using 1

end Sigma2.FockTruncation
