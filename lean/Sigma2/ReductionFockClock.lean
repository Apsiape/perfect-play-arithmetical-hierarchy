import Sigma2.ReductionFockCoordinateRows
import Sigma2.ReductionWitnessArithmetic
import Sigma2.ReductionFiniteWeyl

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 300000
namespace Sigma2.ReductionFockModel
open Sigma2.Tree FockModel
variable (q : ℕ) [NeZero q]

def wave (ζ : ℂ) (hζ : ‖ζ‖=1) : Op := diag q (fun u => ζ^yCoord u.1)
  ⟨1,fun u => by rw [norm_pow,hζ,one_pow]⟩
def phaseOp (ζ : ℂ) : Op := diag q (fun _ => ζ) (bounded_const ζ)
def counter : Op := diag q (fun u => (1/2:ℂ)^yCoord u.1)
  ⟨1,fun u => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (by norm_num)⟩
def pulse : Op := proj q {u | q∣yCoord u.1}
def inverseReader (ζ : ℂ)
    (hsep : ∀ y, 0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖) : Op :=
  diag q (fun u => ReductionWitnessArithmetic.reader q ζ (yCoord u.1))
    ⟨1,fun u => ReductionWitnessArithmetic.reader_bound q ζ hsep _⟩

lemma wave_unitary (ζ : ℂ) (hζ : ‖ζ‖=1) : Unitary (wave q ζ hζ) :=
  diag_unitary q _ _ (fun u => by rw [norm_pow,hζ,one_pow])
lemma phase_unitary (ζ : ℂ) (hζ : ‖ζ‖=1) : Unitary (phaseOp q ζ) :=
  diag_unitary q _ _ (fun _ => hζ)
lemma pulse_projection : Projection (pulse q) := proj_projection q _
lemma inverseReader_contraction (ζ : ℂ)
    (hsep : ∀ y, 0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖) :
    Contraction (inverseReader q ζ hsep) :=
  diag_norm_le q _ _ (fun u => ReductionWitnessArithmetic.reader_bound q ζ hsep _)

lemma counter_positive : PositiveContraction (counter q) := by
  have hp (u : Index q) : 0≤(1/2:ℝ)^yCoord u.1 := by positivity
  have hb (u : Index q) : (1/2:ℝ)^yCoord u.1≤1 :=
    pow_le_one₀ (by norm_num) (by norm_num)
  have hd : Positive (diag q (fun u => ((1-(1/2:ℝ)^yCoord u.1 : ℝ):ℂ))
      ⟨1,fun u => by rw [Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hb u))]; linarith [hp u]⟩) :=
    diag_positive q _ (fun u => sub_nonneg.mpr (hb u)) _
  constructor
  · convert diag_positive q (fun u => (1/2:ℝ)^yCoord u.1) hp
      ⟨1,fun u => by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hp u)]; exact hb u⟩ using 1
    ext v n
    simp [counter,diag_apply]
  · convert hd using 1
    ext v n
    simp [counter,diag_apply,sub_mul]

lemma wave_centralizer (ζ : ℂ) (hζ : ‖ζ‖=1) : Centralizes (density q).op (wave q ζ hζ) :=
  diag_centralizer q _ _
lemma counter_centralizer : Centralizes (density q).op (counter q) := diag_centralizer q _ _
lemma phase_centralizer (ζ : ℂ) : Centralizes (density q).op (phaseOp q ζ) := diag_centralizer q _ _
lemma pulse_centralizer : Centralizes (density q).op (pulse q) := diag_centralizer q _ _
lemma inverseReader_centralizer (ζ : ℂ)
    (hsep : ∀ y, 0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖) :
    Centralizes (density q).op (inverseReader q ζ hsep) := diag_centralizer q _ _

lemma wave_root (ζ : ℂ) (hζ : ‖ζ‖=1) : wave q ζ hζ*root q=root q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  cases w <;> simp [mul_apply_eq_comp,root_basis,wave,diag_basis,yCoord]
lemma counter_root : counter q*root q=root q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  cases w <;> simp [mul_apply_eq_comp,root_basis,counter,diag_basis,yCoord]

lemma wave_rec (ζ : ℂ) (hζ : ‖ζ‖=1) (a : Fin 4) :
    wave q ζ hζ*creation q a=creation q a*
      ((if a.val%2=0 then (1:Op) else phaseOp q ζ)*(wave q ζ hζ*wave q ζ hζ)) := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  fin_cases a <;> simp [mul_apply_eq_comp,creation_basis,wave,phaseOp,diag_basis,
    map_smul,smul_smul,yCoord,pow_add,pow_mul,pow_two,mul_pow,mul_assoc]

lemma counter_rec (a : Fin 4) :
    counter q*creation q a=creation q a*
      ((if a.val%2=0 then (1:ℂ) else 1/2) • (counter q*counter q)) := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  fin_cases a <;> simp [mul_apply_eq_comp,creation_basis,counter,diag_basis,
    map_smul,smul_smul,yCoord,pow_add,pow_mul,pow_two,mul_pow,mul_assoc]

lemma phase_rec (ζ : ℂ) (a : Fin 4) :
    phaseOp q ζ*creation q a=creation q a*phaseOp q ζ := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  simp [mul_apply_eq_comp,creation_basis,phaseOp,diag_basis]

@[simp] lemma pulse_apply (v : H) (n : ℕ) :
    pulse q v n=(if q∣yCoord ((enumeration q).symm n).1 then (1:ℂ) else 0)*v n := by
  by_cases h : q∣yCoord ((enumeration q).symm n).1 <;> simp [pulse,proj,diag_apply,h]

lemma return_row (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q) (hnorm : ‖ζ‖=1) :
    (wave q ζ hnorm-1)*pulse q=0 := by
  ext v n
  let y := yCoord ((enumeration q).symm n).1
  simp only [mul_apply_eq_comp,ContinuousLinearMap.smul_apply,wave,counter,inverseReader,
    diag_apply,pulse_apply,sub_apply,one_apply_eq_self,zero_apply,lp.coeFn_zero,Pi.zero_apply,
    lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  change (ζ^y*((if q∣y then (1:ℂ) else 0)*v n))-
    ((if q∣y then (1:ℂ) else 0)*v n)=0
  have h := ReductionWitnessArithmetic.return_equation q ζ hζ y
  calc
    _ = ((ζ^y-1)*(if q∣y then (1:ℂ) else 0))*v n := by ring
    _ = 0 := by rw [h,zero_mul]

lemma reader_row (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q) (hnorm : ‖ζ‖=1)
    (hsep : ∀ y, 0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖) :
    inverseReader q ζ hsep*(wave q ζ hnorm-1)=
      (1/2:ℂ) • (counter q*(1-pulse q)) := by
  ext v n
  let y := yCoord ((enumeration q).symm n).1
  simp only [mul_apply_eq_comp,ContinuousLinearMap.smul_apply,wave,counter,inverseReader,
    diag_apply,pulse_apply,sub_apply,one_apply_eq_self,zero_apply,lp.coeFn_zero,Pi.zero_apply,
    lp.coeFn_sub,lp.coeFn_smul,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  change ReductionWitnessArithmetic.reader q ζ y*(ζ^y*v n-v n)=
    (1/2:ℂ)*((1/2:ℂ)^y*(v n-(if q∣y then (1:ℂ) else 0)*v n))
  have h := ReductionWitnessArithmetic.reader_equation q ζ hζ y
  calc
    _ = (ReductionWitnessArithmetic.reader q ζ y*(ζ^y-1))*v n := by ring
    _ = ((1/2:ℂ)^(y+1)*(if q∣y then 0 else 1))*v n := by rw [h]
    _ = _ := by rw [pow_succ]; split_ifs <;> ring

#print axioms counter_positive
#print axioms wave_rec
#print axioms counter_rec
#print axioms return_row
#print axioms reader_row
end Sigma2.ReductionFockModel
