import Sigma2.RowGame

noncomputable section
open scoped BigOperators
namespace Sigma2.RowColumns
open Compiler RowGame

def sign (b : Bool) : ℂ := if b then -1 else 1

theorem sign_star (b : Bool) : star (sign b)=sign b := by cases b <;> norm_num [sign]
theorem sign_sq (b : Bool) : sign b*sign b=1 := by cases b <;> norm_num [sign]

theorem reflection_unitary (P : Op) (hP : Projection P) : Unitary ((2:ℂ) • P-1) := by
  have hstar : star ((2:ℂ) • P-1)=(2:ℂ) • P-1 := by
    have hs : star ((2:ℂ) • P)=star (2:ℂ) • star P := star_smul (2:ℂ) P
    have ht : star ((2:ℂ) • P-1)=star ((2:ℂ) • P)-star (1:Op) := star_sub ((2:ℂ) • P) (1:Op)
    rw [ht, hs, star_ofNat, hP.1, star_one]
  have hsquare : ((2:ℂ) • P-1)*((2:ℂ) • P-1)=1 := by
    calc
      _ = (4:ℂ) • (P*P)-(4:ℂ) • P+1 := by
        simp only [sub_mul, mul_sub, smul_mul_smul_comm, smul_mul_assoc,
          mul_smul_comm, mul_one, one_mul]
        module
      _ = 1 := by rw [hP.2]; module
  exact ⟨by rw [hstar, hsquare], by rw [hstar, hsquare]⟩

theorem slot_unitary {n : ℕ} (E : Fin n → Op) (hE : ∀ i, Projection (E i))
    (v : RowSlots.Slot n) : Unitary (v.eval E) := by
  let U : Op := match v.event with | none => 1 | some i => (2:ℂ) • E i-1
  have hu : Unitary U := by
    dsimp [U]
    cases v.event with
    | none => exact ⟨by simp, by simp⟩
    | some i => exact reflection_unitary _ (hE i)
  change Unitary (if v.negative then -U else U)
  split_ifs
  · have hn : star (-U)= -star U := star_neg U
    constructor
    · calc
        _ = star U*U := by rw [hn]; exact neg_mul_neg (star U) U
        _ = 1 := hu.1
    · calc
        _ = U*star U := by rw [hn]; exact neg_mul_neg U (star U)
        _ = 1 := hu.2
  · exact hu
/-- The actual blocks of I_t I_t*. No pairwise commutation of the V_j enters
this definition or the projection proof. This uses d^{-1}, avoiding roots. -/
def column {d : ℕ} (bits : ℕ) (V : Fin d → Op) (t : Fin d) : Matrix (Fin d) (Fin d) Op :=
  fun i j => ((1/(d:ℂ))*sign (parity bits t.val i.val)*sign (parity bits t.val j.val)) •
    (V i*star (V j))

theorem column_star {d : ℕ} (bits : ℕ) (V : Fin d → Op) (t : Fin d) :
    star (column bits V t)=column bits V t := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.star_apply, column, star_smul, star_mul, star_star,
    star_div₀, star_one, star_natCast, sign_star]
  congr 1
  ring

theorem column_idempotent {d : ℕ} (_hd : 0<d) (bits : ℕ) (V : Fin d → Op)
    (hV : ∀ j, Unitary (V j)) (t : Fin d) :
    column bits V t*column bits V t=column bits V t := by
  let c : ℂ := 1/(d:ℂ)
  let s : Fin d → ℂ := fun j => sign (parity bits t.val j.val)
  have hunit (i j k : Fin d) :
      (V i*star (V k))*(V k*star (V j))=V i*star (V j) := by
    calc
      _ = V i*(star (V k)*V k)*star (V j) := by noncomm_ring
      _ = V i*star (V j) := by rw [(hV k).1, mul_one]
  have hs (i j k : Fin d) : (c*s i*s k)*(c*s k*s j)=c*c*s i*s j := by
    calc
      _ = c*c*s i*s j*(s k*s k) := by ring
      _ = c*c*s i*s j := by rw [show s k*s k=1 from sign_sq _]; ring
  apply Matrix.ext
  intro i j
  change (∑ k, ((c*s i*s k) • (V i*star (V k)))*
    ((c*s k*s j) • (V k*star (V j)))) = (c*s i*s j) • (V i*star (V j))
  simp only [smul_mul_smul_comm, hunit, hs, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  dsimp [c]
  field_simp

/-- This is the projection assignment for every column question of the
computed game, with the common dimension and the actual signed slots. -/
def rowColumn {s} (R : Rows s) (E : Fin R.count → Op) (r : Fin R.rowCount)
    (t : Fin (RowSlots.dimension R)) :
    Matrix (Fin (RowSlots.dimension R)) (Fin (RowSlots.dimension R)) Op :=
  column (2*RowSlots.squares R) (fun j => (RowSlots.slot R r j.val).eval E) t

theorem rowColumn_projection {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i, Projection (E i)) (r : Fin R.rowCount) (t : Fin (RowSlots.dimension R)) :
    star (rowColumn R E r t)=rowColumn R E r t ∧
      rowColumn R E r t*rowColumn R E r t=rowColumn R E r t := by
  exact ⟨column_star _ _ _, column_idempotent (RowSlots.dimension_pos R) _ _
    (fun j => slot_unitary E hE (RowSlots.slot R r j.val)) _⟩

#print axioms column_star
#print axioms column_idempotent
#print axioms rowColumn_projection
end Sigma2.RowColumns



