import Sigma2.FockModel

/-! The free-monoid Fock space with a coefficient multiplicity space. -/
noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 100000
namespace Sigma2.FockModel
variable {α β : Type}
abbrev TreeIndex (α β : Type) := List α × β
local instance : DecidableEq (TreeIndex α β) := fun _ _ => Classical.propDecidable _

def prefixInjection (a : α) : TreeIndex α β ↪ TreeIndex α β where
  toFun u := (a::u.1,u.2)
  inj' := by
    rintro ⟨w,i⟩ ⟨v,j⟩ h
    simpa using h

@[simp] lemma prefix_nil_not_mem (a : α) (j : β) :
    ([],j)∉Set.range (prefixInjection a : TreeIndex α β ↪ _) := by
  rintro ⟨⟨w,i⟩,h⟩
  have := congrArg Prod.fst h
  simp [prefixInjection] at this

@[simp] lemma prefix_cons_mem (a b : α) (w : List α) (j : β) :
    (b::w,j)∈Set.range (prefixInjection a : TreeIndex α β ↪ _) ↔ a=b := by
  constructor
  · rintro ⟨⟨v,i⟩,h⟩
    exact (List.cons.inj (congrArg Prod.fst h)).1
  · rintro rfl
    exact ⟨(w,j),rfl⟩

def creation (a : α) : Operator (TreeIndex α β) := shift (prefixInjection a)
def root : Operator (TreeIndex α β) := projection {u | u.1=[]}

@[simp] lemma creation_single (a : α) (w : List α) (i : β) :
    creation a (lp.single 2 (w,i) 1 : Space (TreeIndex α β))=lp.single 2 (a::w,i) 1 :=
  shift_single _ _

lemma creation_isometries (a b : α) :
    star (creation a : Operator (TreeIndex α β))*creation b=if a=b then 1 else 0 := by
  by_cases h : a=b
  · subst b
    rw [if_pos rfl]
    exact shift_isometry (prefixInjection a : TreeIndex α β ↪ _)
  · rw [if_neg h]
    ext v u
    change (shift (prefixInjection a)).adjoint (shift (prefixInjection b) v) u=0
    rw [adjoint_shift_apply]
    change (shift (prefixInjection b) v) (a::u.1,u.2)=0
    apply shift_apply_off
    intro hm
    exact h ((prefix_cons_mem b a u.1 u.2).mp hm).symm

lemma root_projection : star (root : Operator (TreeIndex α β))=root ∧ (root : Operator (TreeIndex α β))*root=root :=
  projection_spec _

/-- The creation ranges partition precisely the nonempty-word coordinates. -/
lemma creation_ranges [Fintype α] :
    (∑ a : α, (creation a : Operator (TreeIndex α β))*star (creation a))=1-root := by
  apply ext_basis
  rintro ⟨w,j⟩
  have ht (a : α) :
      (creation a*star (creation a) : Operator (TreeIndex α β)) (lp.single 2 (w,j) 1)=
        if (w,j)∈Set.range (prefixInjection a : TreeIndex α β ↪ _) then lp.single 2 (w,j) 1 else 0 := by
    have hh := shift_range (prefixInjection a : TreeIndex α β ↪ _)
    change creation a*star (creation a)=_ at hh
    rw [hh,projection_single]
  rw [ContinuousLinearMap.sum_apply]
  simp only [ht]
  change (∑ a, if (w,j)∈Set.range (prefixInjection a : TreeIndex α β ↪ _) then lp.single 2 (w,j) 1 else 0)=
    lp.single 2 (w,j) 1-root (lp.single 2 (w,j) 1)
  rw [root,projection_single]
  cases w with
  | nil => simp only [prefix_nil_not_mem]; simp
  | cons b w => simp only [prefix_cons_mem]; simp

#print axioms creation_isometries
#print axioms creation_ranges
end Sigma2.FockModel
