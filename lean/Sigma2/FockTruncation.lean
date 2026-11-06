import Sigma2.ReductionFockRealization

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 400000
namespace Sigma2.FockTruncation
open Sigma2.Tree Sigma2.ReductionFockModel
variable (q : ℕ) [NeZero q]

def cut (m : ℕ) : Op := proj q {u | u.1.length ≤ m}
def before (m : ℕ) : Op := proj q {u | u.1.length < m}
def top (m : ℕ) : Op := proj q {u | u.1.length = m}
def creation (m : ℕ) (a : Fin 4) : Op := cut q m * ReductionFockModel.creation q a

lemma cut_projection (m : ℕ) : Projection (cut q m) := proj_projection q _
lemma before_projection (m : ℕ) : Projection (before q m) := proj_projection q _
lemma top_projection (m : ℕ) : Projection (top q m) := proj_projection q _

@[simp] lemma cut_basis (m : ℕ) (u : Index q) :
    cut q m (hilbertBasis q u) = if u.1.length ≤ m then hilbertBasis q u else 0 := by
  by_cases h : u.1.length ≤ m <;> simpa [cut,h] using proj_basis q {u | u.1.length ≤ m} u
@[simp] lemma before_basis (m : ℕ) (u : Index q) :
    before q m (hilbertBasis q u) = if u.1.length < m then hilbertBasis q u else 0 := by
  by_cases h : u.1.length < m <;> simpa [before,h] using proj_basis q {u | u.1.length < m} u
@[simp] lemma top_basis (m : ℕ) (u : Index q) :
    top q m (hilbertBasis q u) = if u.1.length = m then hilbertBasis q u else 0 := by
  by_cases h : u.1.length = m <;> simpa [top,h] using proj_basis q {u | u.1.length = m} u

lemma before_eq (m : ℕ) : before q m = cut q m - top q m := by
  apply ambient_ext q
  intro u
  by_cases h₁ : u.1.length < m
  · simp [h₁, show u.1.length ≤ m by omega, show u.1.length ≠ m by omega]
  · by_cases h₂ : u.1.length = m
    · simp [h₁,h₂]
    · simp [h₁,h₂,show ¬u.1.length ≤ m from by omega]

lemma cut_root (m : ℕ) : cut q m * root q = root q := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  cases w <;> simp [mul_apply_eq_comp,root_basis,map_zero]

lemma cut_creation (m : ℕ) (a : Fin 4) :
    cut q m * ReductionFockModel.creation q a = ReductionFockModel.creation q a * before q m := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  simp only [mul_apply_eq_comp,creation_basis,cut_basis,before_basis,List.length_cons]
  by_cases h : w.length < m <;> simp [h, show w.length+1 ≤ m ↔ w.length < m by omega]

lemma before_cut (m : ℕ) : before q m * cut q m = before q m := by
  apply ambient_ext q
  intro u
  by_cases h : u.1.length < m
  · simp [mul_apply_eq_comp,h,show u.1.length ≤ m by omega]
  · simp [mul_apply_eq_comp,h,apply_ite,map_zero]

lemma creation_supported (m : ℕ) (a : Fin 4) :
    cut q m * creation q m a = creation q m a ∧ creation q m a * cut q m = creation q m a := by
  constructor
  · rw [creation, ← mul_assoc, (cut_projection q m).2]
  · rw [creation,cut_creation, mul_assoc,before_cut]

lemma isometries (m : ℕ) (a b : Fin 4) :
    star (creation q m a) * creation q m b =
      if a=b then cut q m - top q m else 0 := by
  simp only [creation,cut_creation,star_mul]
  rw [(before_projection q m).1, mul_assoc, ← mul_assoc (star (ReductionFockModel.creation q a)),
    ReductionFockModel.creation_isometries]
  by_cases h : a=b
  · rw [if_pos h,support,one_mul,(before_projection q m).2,before_eq,if_pos h]
  · simp [h]

lemma ranges (m : ℕ) :
    (∑ a, creation q m a * star (creation q m a)) = cut q m - root q := by
  simp only [creation,star_mul,(cut_projection q m).1]
  calc
    _ = cut q m * (∑ a, ReductionFockModel.creation q a * star (ReductionFockModel.creation q a)) * cut q m := by
      simp only [Finset.mul_sum,Finset.sum_mul,mul_assoc]
    _ = cut q m * (1 - root q) * cut q m := by
      rw [ReductionFockModel.creation_ranges,support]
    _ = cut q m - root q := by
      have hr : root q * cut q m = root q := by
        have h := congrArg star (cut_root q m)
        simpa only [star_mul,(cut_projection q m).1,(root_projection q).1] using h
      rw [mul_sub,mul_one,cut_root,sub_mul,(cut_projection q m).2,hr]

lemma diagonal_defect (m : ℕ) (a : Fin 4) :
    star (creation q m a) * creation q m a - cut q m = -top q m := by
  rw [isometries,if_pos rfl]
  abel

lemma creation_contractive (m : ℕ) (a : Fin 4) : Contraction (creation q m a) := by
  have hc : ‖ReductionFockModel.creation q a‖ ≤ 1 := by
    have h := CStarRing.norm_star_mul_self (x := ReductionFockModel.creation q a)
    rw [ReductionFockModel.creation_isometries,if_pos rfl,support] at h
    have hn : ‖(1:Op)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    nlinarith [norm_nonneg (ReductionFockModel.creation q a)]
  exact (norm_mul_le _ _).trans (by
    simpa only [one_mul] using mul_le_mul (TreeFoundation.projection_norm_le _ (cut_projection q m)) hc
      (norm_nonneg _) zero_le_one)

lemma cut_diag (m : ℕ) (c : Index q → ℂ) (hc) :
    cut q m * diag q c hc = diag q c hc * cut q m :=
  diag_commute q _ _ _ _

lemma cut_perm (m : ℕ) (e : Equiv.Perm (Index q))
    (he : ∀ u, (e u).1.length = u.1.length) :
    cut q m * perm q e = perm q e * cut q m := by
  apply ambient_ext q
  intro u
  by_cases h : u.1.length ≤ m <;> simp [mul_apply_eq_comp,perm_basis,he,h]

#print axioms isometries
#print axioms ranges
#print axioms diagonal_defect
end Sigma2.FockTruncation
