import Sigma2.UpperAmplitudes
import Sigma2.UpperRealArithmeticComplex

noncomputable section
set_option linter.unusedSimpArgs false
open scoped BigOperators InnerProductSpace ComplexOrder Matrix
namespace Sigma2.UpperFiniteOperators

theorem sum_nat_eq (d i : ℕ) (f : Fin d → ℂ) :
    (∑ x : Fin d, if i = x.val then f x else 0) = if hi : i<d then f ⟨i,hi⟩ else 0 := by
  classical
  split_ifs with hi
  · rw [Finset.sum_eq_single (⟨i,hi⟩ : Fin d)]
    · simp
    · intro j _ hj
      have hn : i ≠ j.val := fun h => hj (Fin.ext h.symm)
      simp [hn]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have hn : i ≠ j.val := by intro h; exact hi (h.symm ▸ j.isLt)
    simp [hn]

/-- Embed a finite matrix as a finite-rank operator in the fixed countable model. -/
def extend (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) : Op :=
  ∑ i, ∑ j, A i j • InnerProductSpace.rankOne ℂ (basis i) (basis j)

@[simp] theorem extend_zero (d : ℕ) : extend d 0 = 0 := by simp [extend]

@[simp] theorem extend_add (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    extend d (A+B) = extend d A + extend d B := by
  simp [extend,add_smul,Finset.sum_add_distrib]

@[simp] theorem extend_smul (d : ℕ) (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    extend d (c • A) = c • extend d A := by
  simp [extend,Finset.smul_sum,smul_smul]

@[simp] theorem extend_sum {ι : Type} (s : Finset ι) (d : ℕ)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) :
    extend d (∑ i ∈ s,A i) = ∑ i ∈ s,extend d (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih]

/-- The finite coordinate projection. -/
def cut (d : ℕ) : Op := extend d 1

@[simp] theorem extend_apply (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (v : H) (i : ℕ) :
    extend d A v i = if hi : i < d then ∑ j : Fin d,A ⟨i,hi⟩ j * v j else 0 := by
  classical
  simp only [extend,sum_apply,smul_apply,
    lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,
    InnerProductSpace.rankOne_apply,basis,lp.inner_single_left,RCLike.inner_apply,
    star_one,one_mul,lp.single_apply]
  split_ifs with hi
  · simpa [Pi.single_apply,mul_assoc,hi] using sum_nat_eq d i (fun x => ∑ j,A x j * v j)
  · simpa [Pi.single_apply,mul_assoc,hi] using sum_nat_eq d i (fun x => ∑ j,A x j * v j)

@[simp] theorem extend_entry (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (i j : ℕ) :
    entry (extend d A) i j = if hi : i < d then if hj : j < d then
      A ⟨i,hi⟩ ⟨j,hj⟩ else 0 else 0 := by
  classical
  unfold entry
  rw [extend_apply]
  split_ifs with hi hj
  · simpa [basis,lp.single_apply,Pi.single_apply,eq_comm,hj] using sum_nat_eq d j (A ⟨i,hi⟩)
  · simpa [basis,lp.single_apply,Pi.single_apply,eq_comm,hj] using sum_nat_eq d j (A ⟨i,hi⟩)
  · rfl

@[simp] theorem extend_entry_fin (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    entry (extend d A) i j = A i j := by simp

@[simp] theorem cut_entry (d i j : ℕ) :
    entry (cut d) i j = if i=j ∧ i<d then 1 else 0 := by
  classical
  simp only [cut,extend_entry,Matrix.one_apply]
  split_ifs <;> simp_all
  all_goals omega

@[simp] theorem cut_apply (d : ℕ) (v : H) (i : ℕ) :
    cut d v i = if i<d then v i else 0 := by
  classical
  rw [cut,extend_apply]
  split_ifs with hi
  · simpa only [Matrix.one_apply,Fin.ext_iff,ite_mul,one_mul,zero_mul] using
      (sum_nat_eq d i (fun j => v j)).trans (dite_eq_left hi)
  · rfl

@[simp] theorem cut_mul (d : ℕ) : cut d * cut d = cut d := by
  ext v i
  change cut d (cut d v) i = cut d v i
  by_cases hi : i<d <;> simp [hi]

@[simp] theorem cut_star (d : ℕ) : star (cut d) = cut d := by
  apply UpperAnalytic.entry_ext
  intro i j
  have h := ContinuousLinearMap.adjoint_inner_left (cut d) (basis i) (basis j)
  have he (T : Op) (a b : ℕ) : inner ℂ (basis a) (T (basis b)) = entry T a b := by
    simp [basis,entry,lp.inner_single_left]
  rw [← inner_conj_symm] at h
  simp only [he] at h
  change entry (ContinuousLinearMap.adjoint (cut d)) i j = entry (cut d) i j
  have hh := congrArg (starRingEnd ℂ) h
  simp only [Complex.conj_conj] at hh
  rw [hh,cut_entry,cut_entry]
  have heq : (j=i ∧ j<d) ↔ (i=j ∧ i<d) := by omega
  simp only [heq]
  split_ifs <;> norm_num

/-- Extension respects matrix multiplication. -/
theorem extend_mul (d : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    extend d (A*B) = extend d A * extend d B := by
  classical
  apply UpperAnalytic.entry_ext
  intro i j
  change entry (extend d (A*B)) i j = extend d A (extend d B (basis j)) i
  rw [extend_apply]
  split_ifs with hi
  · simp only [extend_entry,hi,↓reduceDIte]
    split_ifs with hj
    · simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      change A ⟨i,hi⟩ k * B k ⟨j,hj⟩ = A ⟨i,hi⟩ k * entry (extend d B) k j
      simp [hj]
    · symm
      apply Finset.sum_eq_zero
      intro k _
      change A ⟨i,hi⟩ k * entry (extend d B) k j = 0
      simp [hj]
  · simp [extend_entry,hi]

/-- Every matrix extension is compact. -/
theorem extend_compact (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    IsCompactOperator (extend d A) := by
  unfold extend
  have hsum {ι : Type} (s : Finset ι) (T : ι → Op)
      (hT : ∀ i ∈ s,IsCompactOperator (T i)) : IsCompactOperator (∑ i ∈ s,T i : Op) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (isCompactOperator_zero : IsCompactOperator (0 : H → H))
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hT i (Finset.mem_insert_self _ _)).add
        (ih (fun j hj => hT j (Finset.mem_insert_of_mem hj)))
  apply hsum
  intro i _
  apply hsum
  intro j _
  exact (DensitySpectral.rankOne_compact _ _).smul (A i j)

@[simp] theorem cut_mul_extend (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    cut d * extend d A = extend d A := by
  rw [cut,← extend_mul,one_mul]

@[simp] theorem extend_mul_cut (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    extend d A * cut d = extend d A := by
  rw [cut,← extend_mul,mul_one]

/-- Matrix coefficients of the adjoint. -/
theorem entry_star (T : Op) (i j : ℕ) : entry (star T) i j = star (entry T j i) := by
  have h := ContinuousLinearMap.adjoint_inner_left T (basis i) (basis j)
  have he (U : Op) (a b : ℕ) : inner ℂ (basis a) (U (basis b)) = entry U a b := by
    simp [basis,entry,lp.inner_single_left]
  rw [← inner_conj_symm] at h
  simp only [he] at h
  have hh := congrArg (starRingEnd ℂ) h
  rw [ContinuousLinearMap.star_eq_adjoint,RCLike.star_def]
  exact (Complex.conj_conj _).symm.trans hh

@[simp] theorem extend_star (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    extend d A.conjTranspose = star (extend d A) := by
  apply UpperAnalytic.entry_ext
  intro i j
  rw [entry_star]
  simp only [extend_entry,Matrix.conjTranspose_apply]
  by_cases hi : i<d <;> by_cases hj : j<d <;> simp only [hi,hj,↓reduceDIte,star_zero]

/-- Finite matrix positivity is preserved by zero extension. -/
theorem extend_positive (d : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) :
    Positive (extend d A) := by
  obtain ⟨Y,rfl⟩ := (UpperRealArithmetic.positive_iff_factor A).mp hA
  rw [extend_mul,extend_star]
  exact ContinuousLinearMap.nonneg_iff_isPositive.mp (star_mul_self_nonneg _)

/-- Both the coordinate cut and its complement are positive. -/
theorem cut_positive (d : ℕ) : Positive (cut d) ∧ Positive (1-cut d) := by
  have hp : Projection (cut d) := ⟨cut_star d,cut_mul d⟩
  have hpos (P : Op) (hP : Projection P) : Positive P := by
    have he : star P * P = P := by rw [hP.1,hP.2]
    exact he ▸ ContinuousLinearMap.nonneg_iff_isPositive.mp (star_mul_self_nonneg P)
  refine ⟨hpos _ hp,hpos _ ⟨?_,?_⟩⟩
  · change star (1-cut d : Op) = (1-cut d : Op)
    exact IsSelfAdjoint.sub (R := Op) (IsSelfAdjoint.one Op) (cut_star d)
  · rw [mul_sub,sub_mul,sub_mul,one_mul,mul_one,cut_mul]
    abel

/-- Add a fixed deterministic answer on the orthogonal complement. -/
def effect {ι : Type} [DecidableEq ι] (d : ℕ) (a₀ a : ι)
    (A : Matrix (Fin d) (Fin d) ℂ) : Op :=
  extend d A + if a=a₀ then 1-cut d else 0

theorem effect_positive {ι : Type} [DecidableEq ι] (d : ℕ) (a₀ a : ι)
    (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) :
    Positive (effect d a₀ a A) := by
  apply (extend_positive d A hA).add
  split_ifs
  · exact (cut_positive d).2
  · exact ContinuousLinearMap.isPositive_zero

theorem effect_sum {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ) (a₀ : ι)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∑ a,A a=1) :
    ∑ a,effect d a₀ a (A a)=1 := by
  simp only [effect,Finset.sum_add_distrib,← extend_sum,hA]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  change cut d + (1-cut d) = 1
  abel

theorem effect_norm_le_one {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ) (a₀ a : ι)
    (A : ι → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ a,(A a).PosSemidef)
    (hs : ∑ a,A a=1) : ‖effect d a₀ a (A a)‖ ≤ 1 := by
  have hp j := effect_positive d a₀ j (A j) (hA j)
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (hp a))).mpr
  apply sub_nonneg.mp
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  rw [← effect_sum d a₀ A hs]
  exact Preliminaries.positive_sum_erase _ hp a

theorem effect_mul_extend {ι : Type} [DecidableEq ι] (d : ℕ) (a₀ a : ι)
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    effect d a₀ a A * extend d B = extend d (A*B) := by
  unfold effect
  split_ifs <;> simp only [add_mul,zero_mul,add_zero,sub_mul,one_mul,
    cut_mul_extend,sub_self,← extend_mul]

theorem extend_mul_effect {ι : Type} [DecidableEq ι] (d : ℕ) (a₀ a : ι)
    (A B : Matrix (Fin d) (Fin d) ℂ) :
    extend d A * effect d a₀ a B = extend d (A*B) := by
  unfold effect
  split_ifs <;> simp only [mul_add,mul_zero,add_zero,mul_sub,mul_one,
    extend_mul_cut,sub_self,← extend_mul]

/-- Complementary deterministic answers do not contribute to a finite sandwich. -/
theorem effect_sandwich {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (d : ℕ) (a₀ a : ι) (b₀ b : κ) (E D F : Matrix (Fin d) (Fin d) ℂ) :
    effect d a₀ a E * extend d D * effect d b₀ b F = extend d (E*D*F) := by
  rw [effect_mul_extend,extend_mul_effect]

/-- Compression of an infinite operator to the first coordinates. -/
def compress (d : ℕ) (T : Op) : Matrix (Fin d) (Fin d) ℂ := fun i j => entry T i j

theorem compress_positive (d : ℕ) (T : Op) (hp : Positive T) :
    (compress d T).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change star (entry T j i) = entry T i j
    rw [← entry_star,hp.isSelfAdjoint]
  · intro z
    let v : H := ∑ i : Fin d,z i • basis i
    have hinner : inner ℂ v (T v) = star z ⬝ᵥ ((compress d T) *ᵥ z) := by
      simp only [v,map_sum,map_smul,inner_sum,sum_inner,inner_smul_left,inner_smul_right,
        dotProduct,Matrix.mulVec,Pi.star_apply,Finset.mul_sum,compress]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      simp only [basis,entry,lp.inner_single_left,RCLike.inner_apply,star_one,one_mul]
      simp only [RCLike.star_def,map_one,mul_one]
      ring
    rw [← hinner]
    have hh := (ContinuousLinearMap.isPositive_iff T).mp hp |>.2 v
    have he : inner ℂ (T v) v = inner ℂ v (T v) := hp.isSymmetric v v
    exact he ▸ hh

theorem compress_sum {ι : Type} [Fintype ι] (d : ℕ) (A : ι → Op)
    (hs : ∑ i,A i=1) : ∑ i,compress d (A i)=1 := by
  ext i j
  have he := congrArg (fun T : Op => entry T i j) hs
  simpa only [entry,sum_apply,lp.coeFn_sum,Finset.sum_apply,compress,
    Matrix.sum_apply,one_apply_eq_self,basis,lp.single_apply,Pi.single_apply,
    Matrix.one_apply,Fin.ext_iff] using he

end Sigma2.UpperFiniteOperators
