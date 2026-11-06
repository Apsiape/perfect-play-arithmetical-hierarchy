import Sigma2.CompilerEffectivePreGame
noncomputable section
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective
set_option allowUnsafeReducibility true in
attribute [local reducible] CompilerScaffold.rows
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList coefficient rowAt nameAt RowSlots.coefficients encodingCount encodingOffset refinementCount scenario polynomials words structuralPolynomials applicationPolynomials
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.cond
variable {α β : Type} [Primcodable α] [Primcodable β]

@[fun_prop] theorem cnatprod (f : α → List ℕ) (hf : Computable f) :
    Computable (fun a => (f a).prod) := by
  have hc := cfoldr f (fun _ => (1:ℕ)) (fun _ z => z.1*z.2) hf (Computable.const 1)
    (cmul _ _ (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)).to₂
  exact hc.of_eq (fun a => by induction f a <;> simp_all)
@[fun_prop] theorem cratDen (f : α → ℚ) (hf : Computable f) :
    Computable (fun a => (f a).den) := UpperCoding.rat_den.to_comp.comp hf
@[fun_prop] theorem cratNum (f : α → ℚ) (hf : Computable f) :
    Computable (fun a => (f a).num) := UpperCoding.rat_num.to_comp.comp hf
@[fun_prop] theorem cintNat (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => (f a : ℤ)) := UpperCoding.int_ofNat.to_comp.comp hf
@[fun_prop] theorem cintMul (f g : α → ℤ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => f a*g a) := UpperCoding.int_mul.to_comp.comp hf hg
@[fun_prop] theorem cintAbs (f : α → ℤ) (hf : Computable f) :
    Computable (fun a => (f a).natAbs) := UpperCoding.int_natAbs.to_comp.comp hf
@[fun_prop] theorem cintLt (f g : α → ℤ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => decide (f a<g a)) := UpperCoding.int_lt.decide.to_comp.comp hf hg

theorem ofFn_eq_range {σ : Type} {n : ℕ} (f : Fin n → σ) (g : ℕ → σ)
    (h : ∀ i, f i=g i.val) : List.ofFn f=(List.range n).map g := by
  apply List.ext_getElem <;> simp [h]

theorem rowAt_computable : Computable (fun z : Presentation × ℕ => rowAt z.1 z.2) := by
  unfold rowAt
  exact cgetD _ _ (cget _ _ (rowList_computable.comp Computable.fst) Computable.snd) (Computable.const (row []))
theorem nameAt_computable : Computable (fun z : Presentation × ℕ => nameAt z.1 z.2) := by
  unfold nameAt
  exact cgetD _ _ (cget _ _ (names_computable.comp Computable.fst) Computable.snd) (Computable.const (ProjectionName.frame 0))
@[fun_prop] theorem crowAt (P : α → Presentation) (r : α → ℕ) (hP : Computable P) (hr : Computable r) :
    Computable (fun a => rowAt (P a) (r a)) := by
  have hc := rowAt_computable.comp (hP.pair hr)
  exact hc.of_eq (fun a => rfl)
@[fun_prop] theorem cnameAt (P : α → Presentation) (r : α → ℕ) (hP : Computable P) (hr : Computable r) :
    Computable (fun a => nameAt (P a) (r a)) := by
  have hc := nameAt_computable.comp (hP.pair hr)
  exact hc.of_eq (fun a => rfl)
@[fun_prop] theorem ccoefficient (r : α → RationalRow) (p : α → ProjectionName)
    (hr : Computable r) (hp : Computable p) :
    Computable (fun a => coefficient (r a) (p a)) := coefficient_computable.comp (hr.pair hp)

def rationalAt (P : Presentation) (r i : ℕ) : ℚ :=
  if i=0 then (rowAt P r).constant else coefficient (rowAt P r) (nameAt P (i-1))

def denominatorNat (P : Presentation) (r : ℕ) : ℕ :=
  ((List.range ((names P).length+1)).map (fun i => (rationalAt P r i).den)).prod

def productExcept (P : Presentation) (r i : ℕ) : ℕ :=
  ((List.range ((names P).length+1)).map (fun j => if j=i then 1 else (rationalAt P r j).den)).prod

def integerAt (P : Presentation) (r i : ℕ) : ℤ :=
  (rationalAt P r i).num * (productExcept P r i : ℤ)

attribute [local irreducible] rationalAt denominatorNat productExcept integerAt

theorem rationalAt_computable : Computable (fun z : Presentation × ℕ × ℕ => rationalAt z.1 z.2.1 z.2.2) := by
  unfold rationalAt
  fun_prop
@[fun_prop] theorem crationalAt (P : α → Presentation) (r i : α → ℕ)
    (hP : Computable P) (hr : Computable r) (hi : Computable i) :
    Computable (fun a => rationalAt (P a) (r a) (i a)) := rationalAt_computable.comp (hP.pair (hr.pair hi))

theorem denominatorNat_computable : Computable (fun z : Presentation × ℕ => denominatorNat z.1 z.2) := by
  unfold denominatorNat
  fun_prop
theorem productExcept_computable : Computable (fun z : Presentation × ℕ × ℕ => productExcept z.1 z.2.1 z.2.2) := by
  unfold productExcept
  fun_prop
@[fun_prop] theorem cproductExcept (P : α → Presentation) (r i : α → ℕ)
    (hP : Computable P) (hr : Computable r) (hi : Computable i) :
    Computable (fun a => productExcept (P a) (r a) (i a)) := productExcept_computable.comp (hP.pair (hr.pair hi))
theorem integerAt_computable : Computable (fun z : Presentation × ℕ × ℕ => integerAt z.1 z.2.1 z.2.2) := by
  unfold integerAt
  fun_prop

theorem rationalAt_eq (P : Presentation) (r : Fin (rowList P).length) (i : Fin ((names P).length+1)) :
    rationalAt P r.val i.val=RowSlots.coefficients (rows P) r i := by
  refine Fin.cases (n := (names P).length)
    (motive := fun i => rationalAt P r.val i.val=RowSlots.coefficients (rows P) r i) ?_ (fun j => ?_) i
  · simp only [RowSlots.coefficients,Fin.cases_zero]
    change rationalAt P r.val 0=(rows P).constant r
    unfold rationalAt
    rw [if_pos rfl]
    exact (rows_constant_eq P r).symm
  · simp only [RowSlots.coefficients,Fin.cases_succ]
    change rationalAt P r.val (j.val+1)=(rows P).coefficient r j
    unfold rationalAt
    have hj0 : j.val+1≠0 := Nat.succ_ne_zero j.val
    calc
      _ = coefficient (rowAt P r.val) (nameAt P (j.val+1-1)) := ite_eq_right hj0
      _ = coefficient (rowAt P r.val) (nameAt P j.val) := by rw [Nat.add_sub_cancel]
      _ = _ := (rows_coefficient_eq P r j).symm
theorem denominatorNat_eq (P : Presentation) (r : Fin (rowList P).length) :
    denominatorNat P r.val=RowSlots.denominator (RowSlots.coefficients (rows P) r) := by
  have hl := ofFn_eq_range
    (fun i : Fin ((names P).length+1) => (RowSlots.coefficients (rows P) r i).den)
    (fun i => (rationalAt P r.val i).den) (fun i => congrArg Rat.den (rationalAt_eq P r i).symm)
  unfold denominatorNat RowSlots.denominator
  rw [← hl,List.prod_ofFn]
  try rfl

theorem prod_erase_ite {n : ℕ} (f : Fin n → ℕ) (i : Fin n) :
    (∏ j ∈ Finset.univ.erase i, f j) = ∏ j, if j=i then 1 else f j := by
  calc
    _ = ∏ j ∈ Finset.univ.erase i, if j=i then 1 else f j := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [(Finset.mem_erase.mp hj).1]
    _ = _ := Finset.prod_subset (Finset.erase_subset i Finset.univ) (by
      intro j hj hn
      have hji : j=i := by
        by_contra hji
        exact hn (Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩)
      simp [hji])

theorem integerAt_eq (P : Presentation) (r : Fin (rowList P).length) (i : Fin ((names P).length+1)) :
    integerAt P r.val i.val=RowSlots.integerCoefficient (RowSlots.coefficients (rows P) r) i := by
  have hl := ofFn_eq_range
    (fun j : Fin ((names P).length+1) => if j=i then 1 else (RowSlots.coefficients (rows P) r j).den)
    (fun j => if j=i.val then 1 else (rationalAt P r.val j).den)
        (fun j => by
      by_cases hv : j.val=i.val
      · have hj : j=i := Fin.ext hv
        exact (ite_eq_left hj).trans (ite_eq_left hv).symm
      · have hj : j≠i := fun h => hv (congrArg Fin.val h)
        calc
          _ = (RowSlots.coefficients (rows P) r j).den := ite_eq_right hj
          _ = (rationalAt P r.val j.val).den := congrArg Rat.den (rationalAt_eq P r j).symm
          _ = _ := (ite_eq_right hv).symm)
  have hp : productExcept P r.val i.val =
      ∏ j ∈ Finset.univ.erase i, (RowSlots.coefficients (rows P) r j).den := by
    unfold productExcept
    calc
      _ = (List.ofFn (fun j : Fin ((names P).length+1) =>
          if j=i then 1 else (RowSlots.coefficients (rows P) r j).den)).prod := congrArg List.prod hl.symm
      _ = ∏ j, if j=i then 1 else (RowSlots.coefficients (rows P) r j).den := List.prod_ofFn
      _ = _ := (prod_erase_ite (fun j => (RowSlots.coefficients (rows P) r j).den) i).symm
  unfold integerAt RowSlots.integerCoefficient
  exact congrArg₂ (fun (z : ℤ) (n : ℕ) => z*(n:ℤ)) (congrArg Rat.num (rationalAt_eq P r i)) hp

#print axioms rationalAt_computable
#print axioms denominatorNat_computable
#print axioms integerAt_computable
#print axioms denominatorNat_eq
#print axioms integerAt_eq
end Sigma2.CompilerEffectiveCoding