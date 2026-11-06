import Sigma2.ReductionFockClock

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 300000
namespace Sigma2.ReductionFockModel
open Sigma2.Tree FockModel
variable (q : ℕ) [NeZero q]

def finiteShift : Equiv.Perm (Fin q) :=
  (ZMod.finEquiv q).toEquiv.trans ((Equiv.addRight (1 : ZMod q)).symm.trans
    (ZMod.finEquiv q).symm.toEquiv)

def jOp : Op := perm q (Equiv.prodCongr (Equiv.refl Word) (finiteShift q))
def kOp (ζ : ℂ) (hζ : ‖ζ‖=1) : Op :=
  diag q (fun u => ζ^((ZMod.finEquiv q) u.2).val)
    ⟨1,fun u => by rw [norm_pow,hζ,one_pow]⟩

lemma finiteShift_successor (i : Fin q) :
    (ZMod.finEquiv q) (finiteShift q i)+1=(ZMod.finEquiv q) i := by
  simp [finiteShift]

lemma j_unitary : Unitary (jOp q) := perm_unitary q _
lemma k_unitary (ζ : ℂ) (hζ : ‖ζ‖=1) : Unitary (kOp q ζ hζ) :=
  diag_unitary q _ _ (fun u => by rw [norm_pow,hζ,one_pow])
lemma j_centralizer : Centralizes (density q).op (jOp q) :=
  perm_centralizer q _ (fun u => rfl)
lemma k_centralizer (ζ : ℂ) (hζ : ‖ζ‖=1) : Centralizes (density q).op (kOp q ζ hζ) :=
  diag_centralizer q _ _

@[simp] lemma j_basis (w : Word) (i : Fin q) :
    jOp q (hilbertBasis q (w,i))=hilbertBasis q (w,finiteShift q i) := perm_basis q _ _

lemma weyl (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q) (hnorm : ‖ζ‖=1) :
    jOp q*kOp q ζ hnorm=phaseOp q ζ*kOp q ζ hnorm*jOp q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  have h := ReductionFiniteWeyl.successor_phase q ζ hζ ((ZMod.finEquiv q) (finiteShift q i))
  rw [finiteShift_successor] at h
  simp only [mul_apply_eq_comp,j_basis,kOp,phaseOp,diag_basis,map_smul,smul_smul]
  rw [h,mul_comm ζ]

lemma j_rec (a : Fin 4) : jOp q*creation q a=creation q a*jOp q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  simp [mul_apply_eq_comp,j_basis,creation_basis]
lemma k_rec (ζ : ℂ) (hζ : ‖ζ‖=1) (a : Fin 4) :
    kOp q ζ hζ*creation q a=creation q a*kOp q ζ hζ := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  simp [mul_apply_eq_comp,kOp,diag_basis,creation_basis]

lemma phase_scalar (ζ : ℂ) : phaseOp q ζ=ζ • (1:Op) := by
  ext v n
  rfl

lemma phase_commutes (ζ : ℂ) (T : Op) : phaseOp q ζ*T=T*phaseOp q ζ := by
  rw [phase_scalar,smul_mul_assoc,mul_smul_comm,one_mul,mul_one]

#print axioms weyl
#print axioms j_rec
#print axioms k_rec
end Sigma2.ReductionFockModel
