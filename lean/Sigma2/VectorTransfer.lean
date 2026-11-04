import Sigma2.PureTransfer
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.Purification
open Coefficients TensorLifts

@[simp] theorem slice_add (v w : AB) (k : ℕ) : slice (v+w) k=slice v k+slice w k := by
  ext ⟨i,j⟩; rfl
@[simp] theorem slice_sub (v w : AB) (k : ℕ) : slice (v-w) k=slice v k-slice w k := by
  ext ⟨i,j⟩; rfl
@[simp] theorem slice_smul (c : ℂ) (v : AB) (k : ℕ) : slice (c • v) k=c • slice v k := by
  ext ⟨i,j⟩; rfl

/-- A bounded operator acts identically on each environment component. -/
def Amplifies (L Lhat : BipOp) : Prop := ∀ v k,slice (Lhat v) k=L (slice v k)

theorem amplifies_left (A : Op) : Amplifies (left A) (left (amplify A)) := slice_left A

theorem amplifies_right (B : Op) : Amplifies (right B) (right B) := slice_right B

theorem Amplifies.mul {L Lhat R Rhat : BipOp} (hL : Amplifies L Lhat)
    (hR : Amplifies R Rhat) : Amplifies (L*R) (Lhat*Rhat) := by
  intro v k
  change slice (Lhat (Rhat v)) k=L (R (slice v k))
  rw [hL,hR]

theorem Amplifies.add {L Lhat R Rhat : BipOp} (hL : Amplifies L Lhat)
    (hR : Amplifies R Rhat) : Amplifies (L+R) (Lhat+Rhat) := by
  intro v k
  change slice (Lhat v+Rhat v) k=L (slice v k)+R (slice v k)
  rw [slice_add,hL,hR]

theorem Amplifies.sub {L Lhat R Rhat : BipOp} (hL : Amplifies L Lhat)
    (hR : Amplifies R Rhat) : Amplifies (L-R) (Lhat-Rhat) := by
  intro v k
  change slice (Lhat v-Rhat v) k=L (slice v k)-R (slice v k)
  rw [slice_sub,hL,hR]

theorem Amplifies.smul {L Lhat : BipOp} (hL : Amplifies L Lhat) (c : ℂ) :
    Amplifies (c • L) (c • Lhat) := by
  intro v k
  change slice (c • Lhat v) k=c • L (slice v k)
  rw [slice_smul,hL]

/-- A pure amplified word identity descends to every original positive-weight
component. This applies to the calibrated two-party identity without altering
its original component quantifier or either local transport. -/
theorem packed_identity_transfer {s} (S : NormalStrategy s)
    (u : ℕ → AB) (hu : Summable (fun k => ‖u k‖^2))
    (he : ∀ k,u k=(Real.sqrt (S.weight k):ℂ) • S.vector k)
    (L Lhat R Rhat : BipOp) (hL : Amplifies L Lhat) (hR : Amplifies R Rhat)
    (hz : Lhat (pack u hu)=Rhat (pack u hu)) :
    ∀ k,0<S.weight k → L (S.vector k)=R (S.vector k) := by
  intro k hk
  have hh := congrArg (fun v : AB => slice v k) hz
  rw [hL,hR,slice_pack,he,map_smul,map_smul] at hh
  have hc : (Real.sqrt (S.weight k):ℂ)≠0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hk))
  have hc' := congrArg (fun v : AB => (Real.sqrt (S.weight k):ℂ)⁻¹ • v) hh
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hc'

#print axioms packed_identity_transfer
end Sigma2.Purification
