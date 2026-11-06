import Sigma2.FockTruncationWeights
import Sigma2.CornerCompression

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 400000
namespace Sigma2.FockTruncation
open Sigma2.Tree Sigma2.Reduction Sigma2.ReductionFockModel
variable (q : ℕ) [NeZero q]

lemma density_factor (m : ℕ) :
    (density q m).op = ((mass m)⁻¹ : ℂ) • (cut q m * (ReductionFockModel.density q).op) := by
  apply ambient_ext q
  intro u
  simp only [mul_apply_eq_comp,density_basis,ReductionFockModel.density_basis,
    ContinuousLinearMap.smul_apply,map_smul,cut_basis,smul_smul]
  by_cases h : u.1.length ≤ m
  · simp only [h,ite_true,weight]
    push_cast
    rw [div_eq_mul_inv,mul_comm]
  · simp only [h,ite_false,weight,Complex.ofReal_zero,zero_smul,smul_zero]

lemma cut_label (m : ℕ) (M : Automaton) (ζ : ℂ) (hnorm : ‖ζ‖=1)
    (hsep : ∀ y,0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖) (i : ℕ) :
    cut q m * label q M ζ hnorm hsep i = label q M ζ hnorm hsep i * cut q m := by
  by_cases hi : i < 12
  · interval_cases i
    · change cut q m * root q = root q * cut q m
      have h := congrArg star (cut_root q m)
      rw [cut_root]
      symm
      simpa only [star_mul,(cut_projection q m).1,(root_projection q).1] using h
    · exact cut_perm q m _ (fun u => (nextX_geometry u.1).1)
    · exact cut_perm q m _ (fun u => (nextY_geometry u.1).1)
    · exact cut_diag q m _ _
    · exact cut_diag q m _ _
    · exact cut_diag q m _ _
    · exact cut_diag q m _ _
    · exact cut_diag q m _ _
    · exact cut_perm q m _ (fun u => rfl)
    · exact cut_diag q m _ _
    · exact cut_diag q m _ _
    · exact cut_diag q m _ _
  · have he : i = (i-12)+12 := by omega
    rw [he]
    simp only [label]
    split_ifs
    · exact cut_diag q m _ _
    · simp

lemma density_centralizer (m : ℕ) (A : Op) (hc : cut q m * A = A * cut q m)
    (hd : Centralizes (ReductionFockModel.density q).op A) :
    Centralizes (density q m).op A := by
  unfold Centralizes at *
  rw [density_factor,smul_mul_assoc,mul_smul_comm]
  congr 1
  rw [mul_assoc,hd,← mul_assoc,hc,mul_assoc]

@[simp] lemma creation_basis (m : ℕ) (a : Fin 4) (w : Word) (i : Fin q) :
    creation q m a (hilbertBasis q (w,i)) =
      if w.length < m then hilbertBasis q (a::w,i) else 0 := by
  simp only [creation,mul_apply_eq_comp,ReductionFockModel.creation_basis,cut_basis,List.length_cons]
  by_cases h : w.length < m <;> simp [h,show w.length+1 ≤ m ↔ w.length < m by omega]

lemma weight_cons (m : ℕ) (a : Fin 4) (w : Word) (i : Fin q) (hw : w.length < m) :
    weight q m (a::w,i) = (1/16:ℝ)*weight q m (w,i) := by
  simp only [weight,List.length_cons,show w.length+1 ≤ m from by omega,
    show w.length ≤ m from by omega,ite_true,ReductionFockModel.weight_cons]
  ring

lemma modular (m : ℕ) (a : Fin 4) :
    (density q m).op * creation q m a = (1/16:ℂ) • (creation q m a * (density q m).op) := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  by_cases hw : w.length < m
  · simp only [mul_apply_eq_comp,creation_basis,hw,ite_true,density_basis,
      ContinuousLinearMap.smul_apply,map_smul,smul_smul,weight_cons q m a w i hw]
    push_cast
    rfl
  · simp [mul_apply_eq_comp,hw,map_smul]

/-- Exact structural data on the finite-depth Fock corner. -/
def structural (m : ℕ) (M : Automaton) (ζ : ℂ) (hnorm : ‖ζ‖=1)
    (hsep : ∀ y,0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖) :
    Compiler.StructuralRealization (applicationPresentation M) where
  support := cut q m
  support_projection := cut_projection q m
  density := density q m
  density_supported := density_supported q m
  faithful_on := density_faithful_on q m
  label := fun i => cut q m * label q M ζ hnorm hsep i
  creation := creation q m
  label_supported := fun i => CornerCompression.supported _ (cut_projection q m) _ (cut_label q m M ζ hnorm hsep i)
  creation_supported := creation_supported q m
  typed := fun i => CornerCompression.typed _ (cut_projection q m) _
    (cut_label q m M ζ hnorm hsep i) _
    (label_typed q M ζ hnorm hsep i.val (by simpa only [types_length M] using i.isLt))
  creation_contractive := creation_contractive q m
  centralizer := fun i => by
    have hcut : Centralizes (density q m).op (cut q m) := by
      have hright := congrArg star (density_supported q m)
      have hd := (density q m).positive.isSelfAdjoint.star_eq
      have hh : (density q m).op * cut q m = (density q m).op := by
        simpa only [star_mul,(cut_projection q m).1,hd] using hright
      exact hh.trans (density_supported q m).symm
    have hlabel := density_centralizer q m _ (cut_label q m M ζ hnorm hsep i)
      (label_centralizer q M ζ hnorm hsep i)
    unfold Centralizes at *
    rw [← mul_assoc,hcut,mul_assoc,hlabel,← mul_assoc]
  modular := modular q m

#print axioms structural
end Sigma2.FockTruncation
