import Sigma2.CompilerBase

/-! Executable denominator clearing and signed-reflection slots for Lemma 4.3.
Every slot is finite data; no operator or strategy is an input to this code. -/
open scoped BigOperators
namespace Sigma2.RowSlots
open Compiler

variable {n : ℕ}

def denominator (q : Fin n → ℚ) : ℕ := ∏ i, (q i).den

def integerCoefficient (q : Fin n → ℚ) (i : Fin n) : ℤ :=
  (q i).num * (∏ j ∈ Finset.univ.erase i, (q j).den : ℕ)

theorem denominator_pos (q : Fin n → ℚ) : 0 < denominator q := by
  exact Finset.prod_pos (fun i _ => (q i).den_pos)

theorem clear_denominator (q : Fin n → ℚ) (i : Fin n) :
    (denominator q : ℚ) * q i = (integerCoefficient q i : ℚ) := by
  have hp := Finset.mul_prod_erase Finset.univ (fun j => (q j).den) (Finset.mem_univ i)
  have hq : ((q i).num : ℚ) = q i * ((q i).den : ℚ) := (div_eq_iff (by exact_mod_cast (q i).den_ne_zero)).mp (Rat.num_div_den (q i))
  unfold denominator integerCoefficient
  rw [← hp, Nat.cast_mul]
  push_cast
  rw [hq]
  ring

/-- `none` is I; `some i` is the reflection 2 E_i - I. -/
structure Slot (n : ℕ) where
  event : Option (Fin n)
  negative : Bool
  deriving DecidableEq, Repr

def repeated (e : Option (Fin n)) (c : ℤ) : List (Slot n) :=
  List.replicate c.natAbs ⟨e, decide (c < 0)⟩

def coefficients {s} (R : Rows s) (r : Fin R.rowCount) : Fin (R.count+1) → ℚ :=
  Fin.cases (R.constant r) (R.coefficient r)

def c {s} (R : Rows s) (r : Fin R.rowCount) : Fin (R.count+1) → ℤ :=
  integerCoefficient (coefficients R r)

def term (e : Option (Fin n)) (c : ℤ) : List (Slot n) :=
  (List.replicate c.natAbs [⟨none, decide (c<0)⟩, ⟨e, decide (c<0)⟩]).flatten

def raw {s} (R : Rows s) (r : Fin R.rowCount) : List (Slot R.count) :=
  [⟨none, false⟩, ⟨none, true⟩] ++
  term none (c R r 0) ++
  (List.ofFn (fun i : Fin R.count => term (some i) (c R r i.succ))).flatten

/-- A common bound deliberately allows extra padding. The scalar register is
shared by all rows, so the game needs no row-dependent spectator bookkeeping. -/
def bound {s} (R : Rows s) : ℕ :=
  (List.ofFn (fun r : Fin R.rowCount => (raw R r).length)).sum + 1

def squares {s} (R : Rows s) : ℕ := Nat.log 4 (bound R) + 1

def dimension {s} (R : Rows s) : ℕ := 4 ^ squares R

def slots {s} (R : Rows s) (r : Fin R.rowCount) : List (Slot R.count) :=
  raw R r ++ (List.replicate ((dimension R - (raw R r).length)/2)
    [⟨none, false⟩, ⟨none, true⟩]).flatten

def slot {s} (R : Rows s) (r : Fin R.rowCount) (j : ℕ) : Slot R.count :=
  (slots R r)[j]?.getD ⟨none, false⟩

theorem dimension_pos {s} (R : Rows s) : 0 < dimension R := by
  exact pow_pos (by decide) _

theorem squares_pos {s} (R : Rows s) : 0 < squares R := by
  simp only [squares]; omega

theorem slot_zero {s} (R : Rows s) (r : Fin R.rowCount) :
    slot R r 0 = ⟨none, false⟩ := by
  simp [slot, slots, raw]

noncomputable def Slot.eval (E : Fin n → Op) (v : Slot n) : Op :=
  let U := match v.event with
    | none => (1:Op)
    | some i => (2:ℂ) • E i - 1
  if v.negative then -U else U

theorem repeated_sum (E : Fin n → Op) (e : Option (Fin n)) (c : ℤ) :
    ((repeated e c).map (Slot.eval E)).sum =
      (c : ℂ) • (match e with | none => (1:Op) | some i => (2:ℂ) • E i - 1) := by
  simp only [repeated, List.map_replicate, List.sum_replicate, Slot.eval]
  by_cases h : c < 0
  · simp only [h, decide_true, ite_true]
    have hi : c = -(c.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_neg h]; omega
    have hc : (c : ℂ) = -(c.natAbs : ℂ) := by simpa only [Int.cast_neg, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℂ)) hi
    simp only [hc, ← Nat.cast_smul_eq_nsmul ℂ, smul_neg]
    apply ContinuousLinearMap.ext
    intro v
    ext k
    simp [lp.coeFn_smul]
  · simp only [h, decide_false, Bool.false_eq_true, ite_false]
    have hi : c = (c.natAbs : ℤ) := by rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ c)]
    have hc : (c : ℂ) = (c.natAbs : ℂ) := by simpa only [Int.cast_neg, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℂ)) hi
    rw [hc]
    exact (Nat.cast_smul_eq_nsmul ℂ _ _).symm
theorem term_length (e : Option (Fin n)) (c : ℤ) :
    (term e c).length = 2*c.natAbs := by
  simp [term, List.length_flatten, Nat.mul_comm]

theorem raw_length {s} (R : Rows s) (r : Fin R.rowCount) :
    (raw R r).length = 2*(1+(c R r 0).natAbs+∑ i : Fin R.count, (c R r i.succ).natAbs) := by
  simp [raw, List.length_flatten, term_length, List.sum_ofFn, ← Finset.mul_sum]
  ring

theorem raw_le_dimension {s} (R : Rows s) (r : Fin R.rowCount) :
    (raw R r).length ≤ dimension R := by
  have hh : (raw R r).length ≤
      (List.ofFn (fun r : Fin R.rowCount => (raw R r).length)).sum := by
    apply List.le_sum_of_mem
    exact List.mem_ofFn.mpr ⟨r,rfl⟩
  have hb : bound R < dimension R := Nat.lt_pow_succ_log_self (by decide) (bound R)
  dsimp [bound] at hb
  omega

theorem slots_length {s} (R : Rows s) (r : Fin R.rowCount) :
    (slots R r).length=dimension R := by
  have hl := raw_le_dimension R r
  have he := raw_length R r
  have hd : dimension R % 2=0 := by
    unfold dimension
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (squares_pos R))
    rw [hk, pow_succ]
    omega
  have hp : (dimension R-(raw R r).length)%2=0 := by omega
  simp only [slots, List.length_append, List.length_flatten, List.map_replicate,
    List.length_cons, List.length_nil, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  omega

theorem term_sum (E : Fin n → Op) (e : Option (Fin n)) (c : ℤ) :
    ((term e c).map (Slot.eval E)).sum =
      (c : ℂ) • ((1:Op)+(match e with | none => (1:Op) | some i => (2:ℂ) • E i - 1)) := by
  have hh : ((term e c).map (Slot.eval E)).sum =
      ((repeated none c).map (Slot.eval E)).sum +
      ((repeated e c).map (Slot.eval E)).sum := by
    simp only [term, repeated, List.map_flatten, List.map_replicate, List.sum_flatten,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      List.sum_replicate, nsmul_add]
  rw [hh, repeated_sum, repeated_sum]
  module

/-- The unpadded slots already have exactly the requested row sum. -/
theorem raw_sum {s} (R : Rows s) (r : Fin R.rowCount) (E : Fin R.count → Op) :
    ((raw R r).map (Slot.eval E)).sum =
      (2*(denominator (coefficients R r):ℂ)) •
        ((R.constant r:ℂ) • (1:Op)+∑ i, (R.coefficient r i:ℂ) • E i) := by
  have hc (i : Fin (R.count+1)) :
      (c R r i:ℂ)=(denominator (coefficients R r):ℂ)*(coefficients R r i:ℂ) := by
    exact_mod_cast (clear_denominator (coefficients R r) i).symm
  have hi (i : Fin R.count) :
      (1:Op)+((2:ℂ) • E i-1)=(2:ℂ) • E i := by abel
  simp only [raw, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Slot.eval, Bool.false_eq_true, ite_false, ite_true,
    add_zero, add_neg_cancel, zero_add, term_sum, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply, term_sum, hi, hc, coefficients, Fin.cases_zero, Fin.cases_succ]
  simp only [smul_add, Finset.smul_sum, smul_smul]
  congr 1
  · module
  · apply Finset.sum_congr rfl
    intro i _
    module

/-- Padding contributes only cancelling I,-I pairs. -/
theorem slots_sum {s} (R : Rows s) (r : Fin R.rowCount) (E : Fin R.count → Op) :
    ((slots R r).map (Slot.eval E)).sum =
      (2*(denominator (coefficients R r):ℂ)) •
        ((R.constant r:ℂ) • (1:Op)+∑ i, (R.coefficient r i:ℂ) • E i) := by
  simp only [slots, List.map_append, List.sum_append, List.map_flatten,
    List.map_replicate, List.sum_flatten, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Slot.eval, Bool.false_eq_true, ite_false,
    ite_true, add_zero, add_neg_cancel, List.sum_replicate, nsmul_zero, add_zero]
  exact raw_sum R r E

#print axioms clear_denominator
#print axioms slots_length
#print axioms slots_sum
end Sigma2.RowSlots



