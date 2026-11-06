import Sigma2.ReductionFockModel
import Sigma2.FockPermutations
import Sigma2.FockCoordinates

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 300000
namespace Sigma2.ReductionFockModel
open Sigma2.Tree FockModel
variable (q : ℕ) [NeZero q]
local instance : DecidableEq (Index q) := fun _ _ => Classical.propDecidable _

def diag (c : Index q → ℂ) (hc : Bounded c) : Op :=
  FockModel.diagonal (fun n => c ((enumeration q).symm n))
    ⟨hc.choose,fun n => hc.choose_spec _⟩

@[simp] lemma diag_apply (c : Index q → ℂ) (hc) (v : H) (n : ℕ) :
    diag q c hc v n=c ((enumeration q).symm n)*v n := rfl

@[simp] lemma diag_basis (c : Index q → ℂ) (hc) (u : Index q) :
    diag q c hc (hilbertBasis q u)=c u • hilbertBasis q u := by
  rw [hilbertBasis,FockModel.basis_eq]
  ext n
  by_cases h : n=enumeration q u
  · subst n; simp [diag_apply,Sigma2.basis,lp.single_apply]
  · simp [diag_apply,Sigma2.basis,lp.single_apply,h,Ne.symm h]

lemma diag_mul (c d : Index q → ℂ) (hc) (hd) :
    diag q c hc*diag q d hd=diag q (fun u => c u*d u) (bounded_mul hc hd) := by
  ext v n; simp; ring

lemma diag_star (c : Index q → ℂ) (hc) :
    star (diag q c hc)=diag q (fun u => star (c u)) (bounded_star hc) :=
  FockModel.diagonal_star _ _

lemma diag_commute (c d : Index q → ℂ) (hc) (hd) :
    diag q c hc*diag q d hd=diag q d hd*diag q c hc := by
  ext v n; simp; ring

lemma diag_centralizer (c : Index q → ℂ) (hc) : Centralizes (density q).op (diag q c hc) := by
  apply ambient_ext q
  intro u
  simp only [mul_apply_eq_comp,diag_basis,density_basis,map_smul,smul_smul]
  rw [mul_comm]

lemma diag_norm_le (c : Index q → ℂ) (hc) (h : ∀ u, ‖c u‖≤1) :
    ‖diag q c hc‖≤1 := FockModel.diagonal_norm_le _ _ 1 zero_le_one (fun n => h _)

lemma diag_positive (p : Index q → ℝ) (hp : ∀ u, 0≤p u)
    (hb : Bounded (fun u => (p u : ℂ))) : Positive (diag q (fun u => (p u : ℂ)) hb) :=
  FockModel.diagonal_positive _ (fun n => hp _) _

lemma diag_unitary (c : Index q → ℂ) (hc) (h : ∀ u, ‖c u‖=1) :
    Unitary (diag q c hc) := by
  rw [Unitary,diag_star]
  constructor <;> apply ambient_ext q <;> intro u <;>
    simp only [mul_apply_eq_comp,diag_basis,map_smul,smul_smul,one_apply]
  all_goals
    change _ • hilbertBasis q u=hilbertBasis q u
    simp [Complex.star_def,Complex.mul_conj,Complex.normSq_eq_norm_sq,h,mul_comm]

def proj (s : Set (Index q)) : Op := diag q (fun u => if u∈s then 1 else 0)
  ⟨1,fun u => by dsimp; split_ifs <;> norm_num⟩

lemma proj_projection (s : Set (Index q)) : Projection (proj q s) := by
  constructor
  · rw [proj,diag_star]
    congr 1
    funext u
    split_ifs <;> simp
  · apply ambient_ext q
    intro u
    simp only [mul_apply_eq_comp,proj,diag_basis,map_smul,smul_smul]
    split_ifs <;> simp

@[simp] lemma proj_basis (s : Set (Index q)) (u : Index q) :
    proj q s (hilbertBasis q u)=if u∈s then hilbertBasis q u else 0 := by
  rw [proj,diag_basis]
  split_ifs <;> simp

def perm (e : Equiv.Perm (Index q)) : Op := lift q (FockModel.permutation e)

@[simp] lemma perm_basis (e : Equiv.Perm (Index q)) (u : Index q) :
    perm q e (hilbertBasis q u)=hilbertBasis q (e u) := by
  simp only [perm,lift_basis,FockModel.permutation_single]
  exact (hilbertBasis q).repr_symm_single _

lemma perm_star (e : Equiv.Perm (Index q)) : star (perm q e)=perm q e.symm := by
  rw [perm,← map_star,FockModel.permutation_star]
  rfl

lemma perm_unitary (e : Equiv.Perm (Index q)) : Unitary (perm q e) := by
  have h := FockModel.permutation_unitary e
  exact ⟨by simpa only [perm,map_mul,map_star,map_one] using congrArg (lift q) h.1,
    by simpa only [perm,map_mul,map_star,map_one] using congrArg (lift q) h.2⟩

lemma perm_centralizer (e : Equiv.Perm (Index q))
    (he : ∀ u, (e u).1.length=u.1.length) : Centralizes (density q).op (perm q e) := by
  apply ambient_ext q
  intro u
  simp only [mul_apply_eq_comp,perm_basis,density_basis,map_smul]
  congr 1
  simp only [ReductionFockWeights.weight,fockWeight,he]

#print axioms diag_centralizer
#print axioms diag_unitary
#print axioms proj_projection
#print axioms perm_unitary
#print axioms perm_centralizer
end Sigma2.ReductionFockModel
