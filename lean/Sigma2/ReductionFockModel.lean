import Sigma2.FockTree
import Sigma2.FockDensity
import Sigma2.ReductionFockWeights

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
namespace Sigma2.ReductionFockModel
open Sigma2.Tree
open FockModel
variable (q : ℕ) [NeZero q]

abbrev Index (q : ℕ) := Word × Fin q

/-- Scan the explicit Encodable code range; the list multiplicity makes it infinite. -/
def enumeration : Index q ≃ ℕ := by
  letI : Nonempty (Fin q) := ⟨⟨0,NeZero.pos q⟩⟩
  letI : Denumerable (Index q) := Denumerable.ofEncodableOfInfinite (Index q)
  exact Denumerable.eqv (Index q)

attribute [local irreducible] enumeration
local instance : DecidableEq (Index q) := fun _ _ => Classical.propDecidable _

def hilbertBasis : HilbertBasis (Index q) ℂ H := FockModel.basis (enumeration q)

def lift : FockModel.Operator (Index q) ≃⋆ₐ[ℂ] Op :=
  (reindex (enumeration q)).symm.conjStarAlgEquiv

@[simp] lemma lift_basis (T : FockModel.Operator (Index q)) (u : Index q) :
    lift q T (hilbertBasis q u)=
      (reindex (enumeration q)).symm (T (lp.single 2 u 1)) := by
  change (reindex (enumeration q)).symm (T ((reindex (enumeration q)) (hilbertBasis q u)))=_
  rw [show reindex (enumeration q) (hilbertBasis q u)=lp.single 2 u 1 from
    (hilbertBasis q).repr_self u]

lemma ambient_ext (A B : Op) (h : ∀ u : Index q, A (hilbertBasis q u)=B (hilbertBasis q u)) :
    A=B := by
  apply FockModel.ext_basis
  intro n
  obtain ⟨u,rfl⟩ := (enumeration q).surjective n
  have hh := h u
  rw [hilbertBasis,FockModel.basis_eq] at hh
  convert hh using 1 <;> congr 1 <;> ext j <;> simp [Sigma2.basis,lp.single_apply,Pi.single_apply]

def creation (a : Fin 4) : Op := lift q (FockModel.creation a)
def root : Op := lift q (FockModel.root : FockModel.Operator (Index q))
def support (_q : ℕ) : Op := 1

lemma support_projection : Projection (support q) := by
  simp [Projection,support]

lemma supported (T : Op) : support q*T=T ∧ T*support q=T := by simp [support]

lemma root_projection : Projection (root q) := by
  have h := FockModel.root_projection (α := Fin 4) (β := Fin q)
  exact ⟨by simpa only [root,map_star] using congrArg (lift q) h.1,
    by simpa only [root,map_mul] using congrArg (lift q) h.2⟩

lemma creation_isometries (a b : Fin 4) :
    star (creation q a)*creation q b=if a=b then support q else 0 := by
  have h := congrArg (lift q) (FockModel.creation_isometries (β := Fin q) a b)
  simpa only [creation,support,map_mul,map_star,apply_ite,map_one,map_zero] using h

lemma creation_ranges :
    (∑ a,creation q a*star (creation q a))=support q-root q := by
  have h := congrArg (lift q) (FockModel.creation_ranges (α := Fin 4) (β := Fin q))
  simpa only [creation,support,root,map_sum,map_mul,map_star,map_sub,map_one] using h

@[simp] lemma creation_basis (a : Fin 4) (w : Word) (i : Fin q) :
    creation q a (hilbertBasis q (w,i))=hilbertBasis q (a::w,i) := by
  simp only [creation,lift_basis,FockModel.creation_single]
  exact (hilbertBasis q).repr_symm_single (a::w,i)

@[simp] lemma root_basis (u : Index q) :
    root q (hilbertBasis q u)=if u.1=[] then hilbertBasis q u else 0 := by
  rw [root,lift_basis]
  simp only [FockModel.root,FockModel.projection_single,Set.mem_setOf_eq]
  split_ifs
  · exact (hilbertBasis q).repr_symm_single u
  · exact map_zero _

def probability (n : ℕ) : ℝ := ReductionFockWeights.weight q ((enumeration q).symm n)

lemma probability_pos (n : ℕ) : 0<probability q n :=
  ReductionFockWeights.weight_pos q (NeZero.pos q) _

lemma probability_mass : Summable (probability q) ∧ (∑' n,probability q n)=1 := by
  have h := ReductionFockWeights.mass q (NeZero.pos q)
  exact ⟨(enumeration q).symm.summable_iff.mpr h.1,
    ((enumeration q).symm.tsum_eq _).trans h.2⟩

lemma probability_entropy : Summable (fun n => entropyTerm (probability q n)) ∧
    (∑' n,entropyTerm (probability q n))=
      Real.log (4/3)/Real.log 2+4/3+Real.log q/Real.log 2 := by
  have h := ReductionFockWeights.entropy q (NeZero.pos q)
  exact ⟨(enumeration q).symm.summable_iff.mpr h.1,
    ((enumeration q).symm.tsum_eq _).trans h.2⟩

def density : Density := diagonalDensity (probability q) (fun n => (probability_pos q n).le)
  (probability_mass q).1 (probability_mass q).2

lemma density_faithful : Faithful (density q) :=
  diagonalDensity_faithful _ (probability_pos q) (probability_mass q).1 (probability_mass q).2

lemma density_finiteEntropy : FiniteDensityEntropy (density q) :=
  diagonalDensity_finiteEntropy _ _ _ _ (probability_entropy q).1

@[simp] lemma density_basis (u : Index q) :
    (density q).op (hilbertBasis q u)=
      (ReductionFockWeights.weight q u : ℂ) • hilbertBasis q u := by
  rw [hilbertBasis,FockModel.basis_eq]
  change (diagonal (fun n => (probability q n : ℂ)) _) (Sigma2.basis (enumeration q u))=_
  ext n
  change (probability q n : ℂ)*(Sigma2.basis (enumeration q u) n)=
    (ReductionFockWeights.weight q u : ℂ)*(Sigma2.basis (enumeration q u) n)
  by_cases h : n=enumeration q u
  · subst n; simp [diagonal_apply,Sigma2.basis,lp.single_apply,probability]
  · simp [diagonal_apply,Sigma2.basis,lp.single_apply,h,Ne.symm h]

lemma weight_cons (a : Fin 4) (w : Word) (i : Fin q) :
    ReductionFockWeights.weight q (a::w,i)=
      (1/16:ℝ)*ReductionFockWeights.weight q (w,i) := by
  unfold ReductionFockWeights.weight fockWeight
  simp only [List.length_cons,pow_succ]
  ring

lemma modular (a : Fin 4) :
    (density q).op*creation q a=(1/16:ℂ) • (creation q a*(density q).op) := by
  apply ambient_ext q
  rintro ⟨w,i⟩
  simp only [mul_apply_eq_comp,creation_basis,density_basis,map_smul,
    ContinuousLinearMap.smul_apply,smul_smul]
  rw [weight_cons]
  push_cast
  rfl

#print axioms creation_isometries
#print axioms creation_ranges
#print axioms density_faithful
#print axioms density_finiteEntropy
#print axioms modular
end Sigma2.ReductionFockModel
