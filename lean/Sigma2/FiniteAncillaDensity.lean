import Sigma2.FiniteAncillaState

noncomputable section
open scoped BigOperators InnerProductSpace ComplexOrder
namespace Sigma2.FiniteAncilla
open Coefficients FiniteSum TensorLifts
variable (d : ℕ) [NeZero d]

@[simp] theorem fiber_basis (a b : Fin d) (j : ℕ) :
    fiber (coordinates d) (basis (coordinates d (b,j))) a=
      if a=b then basis j else 0 := by
  ext i
  have he : coordinates d (a,i)=coordinates d (b,j) ↔ a=b ∧ i=j := by
    rw [Equiv.apply_eq_iff_eq,Prod.mk.injEq]
  by_cases hab : a=b <;> by_cases hij : i=j <;>
    simp only [fiber_apply,basis,lp.single_apply,Pi.single_apply,he,hab,hij,and_self,
      and_true,and_false,false_and,true_and,ite_true,ite_false,lp.coeFn_zero,Pi.zero_apply,
      apply_ite,Equiv.apply_eq_iff_eq,Prod.mk.injEq]


@[simp] theorem amplify_entry (A : Op) (a b : Fin d) (i j : ℕ) :
    entry (amplify d A) (coordinates d (a,i)) (coordinates d (b,j))=
      if a=b then entry A i j else 0 := by
  unfold entry
  rw [amplify_apply,fiber_basis]
  split_ifs <;> simp

@[simp] theorem entry_smul (c : ℂ) (A : Op) (i j : ℕ) :
    entry (c • A) i j=c*entry A i j := rfl

theorem normalized_diagonal (h : Density) (a : Fin d) (i : ℕ) :
    (entry ((1/(d:ℂ)) • amplify d h.op) (coordinates d (a,i)) (coordinates d (a,i))).re=
      (1/(d:ℝ))*(entry h.op i i).re := by
  rw [entry_smul,amplify_entry,if_pos rfl]
  simp [Complex.mul_re]

theorem repeated_diagonal_summable (h : Density) :
    Summable (fun p : Fin d × ℕ => (1/(d:ℝ))*(entry h.op p.2 p.2).re) := by
  apply (summable_prod_of_nonneg (fun p => ?_)).mpr
  · exact ⟨fun a => h.diagonal_summable.mul_left _,(hasSum_fintype _).summable⟩
  · apply mul_nonneg (by positivity)
    simpa [basis,entry,lp.inner_single_left] using h.positive.re_inner_nonneg_right (basis p.2)

/-- Tensoring a density with the normalized identity on the finite register. -/
def density (h : Density) : Density where
  op := (1/(d:ℂ)) • amplify d h.op
  positive := (amplify_positive d h.op h.positive).smul_of_nonneg (by
    simp [Complex.le_def])
  diagonal_summable := by
    apply (coordinates d).summable_iff.mp
    change Summable (fun p : Fin d × ℕ =>
      (entry ((1/(d:ℂ)) • amplify d h.op) (coordinates d (p.1,p.2)) (coordinates d (p.1,p.2))).re)
    simp_rw [normalized_diagonal]
    exact repeated_diagonal_summable d h
  trace_one := by
    rw [← (coordinates d).tsum_eq]
    change (∑' p : Fin d × ℕ,
      (entry ((1/(d:ℂ)) • amplify d h.op) (coordinates d (p.1,p.2)) (coordinates d (p.1,p.2))).re)=1
    simp_rw [normalized_diagonal]
    rw [(repeated_diagonal_summable d h).tsum_prod,tsum_fintype]
    simp_rw [tsum_mul_left,h.trace_one,mul_one]
    have hd : (d:ℝ)≠0 := by exact_mod_cast NeZero.ne d
    simp [hd]

@[simp] theorem density_entry (h : Density) (a b : Fin d) (i j : ℕ) :
    entry (density d h).op (coordinates d (a,i)) (coordinates d (b,j))=
      if a=b then (1/(d:ℂ))*entry h.op i j else 0 := by
  change (1/(d:ℂ))*entry (amplify d h.op) _ _=_
  rw [amplify_entry]
  split_ifs <;> simp

theorem amplitude_product (z w : ℂ) :
    (amplitude d*z)*star (amplitude d*w)=(1/(d:ℂ))*(z*star w) := by
  rw [star_mul,amplitude_star]
  calc
    _ = (amplitude d*amplitude d)*(z*star w) := by ring
    _ = _ := by rw [amplitude_square]; push_cast; rfl

theorem entangle_coefficient (v : AB) (a b c : Fin d) (i j k : ℕ) :
    entangle d v (coordinates d (a,i),coordinates d (c,k))*
      star (entangle d v (coordinates d (b,j),coordinates d (c,k)))=
    if a=b then (if c=a then (1/(d:ℂ))*(v (i,k)*star (v (j,k))) else 0) else 0 := by
  by_cases hab : a=b
  · subst b
    by_cases hca : c=a
    · subst c; simp only [entangle_apply,ite_true]; exact amplitude_product d _ _
    · simp only [entangle_apply,if_neg hca,if_neg (Ne.symm hca),ite_true,map_zero,star_zero,mul_zero,zero_mul]
  · by_cases hac : a=c
    · subst c
      have hba : b≠a := Ne.symm hab
      simp only [entangle_apply,if_neg hab,if_neg hba,ite_true,map_zero,star_zero,mul_zero,zero_mul]
    · simp only [entangle_apply,if_neg hab,if_neg hac,map_zero,mul_zero,zero_mul]

theorem entangle_marginalA (v : AB) (a b : Fin d) (i j : ℕ) :
    (∑' k,entangle d v (coordinates d (a,i),k)*star (entangle d v (coordinates d (b,j),k)))=
      if a=b then (1/(d:ℂ))*(∑' k,v (i,k)*star (v (j,k))) else 0 := by
  have hs := (coefficient_summable (fun k => column (entangle d v) k)
    (column_mass (entangle d v)).1 (coordinates d (a,i)) (coordinates d (b,j))).comp_injective
    (coordinates d).injective
  change Summable (fun p : Fin d × ℕ => entangle d v (coordinates d (a,i),coordinates d p)*
    star (entangle d v (coordinates d (b,j),coordinates d p))) at hs
  rw [← (coordinates d).tsum_eq,hs.tsum_prod,tsum_fintype]
  simp_rw [entangle_coefficient]
  by_cases hab : a=b
  · simp only [hab,ite_true]
    rw [Finset.sum_eq_single b]
    · simp only [ite_true,tsum_mul_left]
    · intro c hc hcb; simp only [if_neg hcb,tsum_zero]
    · simp
  · simp [hab]

/-- The exact original A marginal, tensored with I/d, is the enlarged marginal. -/
theorem marginalA {s} (S : NormalStrategy s) (h : Density) (hm : MarginalA S h) :
    MarginalA (strategy d S) (density d h) := by
  intro i j
  obtain ⟨⟨a,i⟩,rfl⟩ := (coordinates d).surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := (coordinates d).surjective j
  rw [density_entry]
  change _=∑' k,(S.weight k:ℂ)*∑' l,entangle d (S.vector k) (coordinates d (a,i),l)*
    star (entangle d (S.vector k) (coordinates d (b,j),l))
  simp_rw [entangle_marginalA]
  by_cases hab : a=b
  · simp only [hab,ite_true]
    rw [hm i j,← tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  · simp [hab]

/-- Exchanging the parties exchanges the two ancillary registers as well. -/
theorem entangle_swap (v : AB) : entangle d (swap v)=swap (entangle d v) := by
  ext ⟨i,j⟩
  obtain ⟨⟨a,i⟩,rfl⟩ := (coordinates d).surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := (coordinates d).surjective j
  simp only [entangle_apply,swap_apply]
  by_cases hab : a=b
  · subst b; simp only [ite_true]
  · simp only [if_neg hab,if_neg (Ne.symm hab)]

theorem entangle_marginalB (v : AB) (a b : Fin d) (i j : ℕ) :
    (∑' k,entangle d v (k,coordinates d (a,i))*star (entangle d v (k,coordinates d (b,j))))=
      if a=b then (1/(d:ℂ))*(∑' k,v (k,i)*star (v (k,j))) else 0 := by
  simpa only [entangle_swap,swap_apply] using entangle_marginalA d (swap v) a b i j

/-- Both original mixed-state marginals receive the same finite factor. -/
theorem marginalB {s} (S : NormalStrategy s) (h : Density) (hm : MarginalB S h) :
    MarginalB (strategy d S) (density d h) := by
  intro i j
  obtain ⟨⟨a,i⟩,rfl⟩ := (coordinates d).surjective i
  obtain ⟨⟨b,j⟩,rfl⟩ := (coordinates d).surjective j
  rw [density_entry]
  change _=∑' k,(S.weight k:ℂ)*∑' l,entangle d (S.vector k) (l,coordinates d (a,i))*
    star (entangle d (S.vector k) (l,coordinates d (b,j)))
  simp_rw [entangle_marginalB]
  by_cases hab : a=b
  · simp only [hab,ite_true]
    rw [hm i j,← tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  · simp [hab]

end Sigma2.FiniteAncilla
