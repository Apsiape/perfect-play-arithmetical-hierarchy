import Sigma2.RowWalsh
import Mathlib.Data.Matrix.Basis

noncomputable section
open scoped BigOperators
namespace Sigma2.RowWalsh
open Compiler RowGame RowColumns

/-- Entry form of graph containment. The equation is read from the (i,0)
entry of the forbidden two-coordinate graph product, including the anchor. -/
theorem column_containment (n : ℕ) (V : Fin (2^n) → Op)
    (hV : ∀ j,Unitary (V j)) (C : Matrix (Fin (2^n)) (Fin (2^n)) Op)
    (t o : Fin (2^n))
    (hrow : ∀ i j,C i j*V j=sign (parity n t.val j.val) • C i o) :
    C*column n V t=C := by
  let c : ℂ := 1/((2^n:ℕ):ℂ)
  let s := fun j : Fin (2^n) => sign (parity n t.val j.val)
  have hentry (i j : Fin (2^n)) : C i j=s j • (C i o*star (V j)) := by
    calc
      C i j = (C i j*V j)*star (V j) := by rw [mul_assoc,(hV j).2,mul_one]
      _ = s j • (C i o*star (V j)) := by rw [hrow,smul_mul_assoc]
  apply Matrix.ext
  intro i j
  change (∑ k,C i k*((c*s k*s j) • (V k*star (V j))))=C i j
  have he (k : Fin (2^n)) :
      C i k*((c*s k*s j) • (V k*star (V j)))=
        (c*s j) • (C i o*star (V j)) := by
    calc
      _ = (c*s k*s j) • ((C i k*V k)*star (V j)) := by
        rw [mul_smul_comm]
        congr 1
      _ = ((c*s k*s j)*s k) • (C i o*star (V j)) := by
        rw [hrow,smul_mul_assoc,smul_smul]
      _ = (c*s j) • (C i o*star (V j)) := by
        congr 1
        calc
          _ = c*s j*(s k*s k) := by ring
          _ = c*s j := by rw [show s k*s k=1 from sign_sq _]; ring
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,← Nat.cast_smul_eq_nsmul ℂ,smul_smul]
  rw [hentry i j]
  congr 1
  dsimp [c]
  have hn : ((2^n:ℕ):ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.two_pow_pos n))
  field_simp

/-- Completeness forces equality with the whole Walsh partition. There is no
rank assumption, trace comparison, or commutation between distinct V_j. -/
theorem column_unique_total (n : ℕ) (V : Fin (2^n) → Op) (hV : ∀ j,Unitary (V j))
    (C : Fin (2^n) → Matrix (Fin (2^n)) (Fin (2^n)) Op)
    (A : Matrix (Fin (2^n)) (Fin (2^n)) Op) (hs : ∑ t,C t=A) (o : Fin (2^n))
    (hrow : ∀ t i j,C t i j*V j=sign (parity n t.val j.val) • C t i o) :
    ∀ t,C t=A*column n V t := by
  have hc (t : Fin (2^n)) : C t*column n V t=C t := column_containment n V hV (C t) t o (hrow t)
  intro t
  have hcross (u : Fin (2^n)) (hut : u≠t) : C u*column n V t=0 := by
    calc
      _ = (C u*column n V u)*column n V t := by rw [hc u]
      _ = C u*(column n V u*column n V t) := by rw [mul_assoc]
      _ = 0 := by rw [column_mul_ne n V hV u t hut,mul_zero]
  calc
    C t = C t*column n V t := (hc t).symm
    _ = (∑ u,C u)*column n V t := by
      rw [Finset.sum_mul,Finset.sum_eq_single t]
      · intro u _ hut; exact hcross u hut
      · simp
    _ = A*column n V t := by rw [hs]

theorem column_unique (n : ℕ) (V : Fin (2^n) → Op) (hV : ∀ j,Unitary (V j))
    (C : Fin (2^n) → Matrix (Fin (2^n)) (Fin (2^n)) Op)
    (hs : ∑ t,C t=1) (o : Fin (2^n))
    (hrow : ∀ t i j,C t i j*V j=sign (parity n t.val j.val) • C t i o) :
    ∀ t,C t=column n V t := by
  simpa only [one_mul] using column_unique_total n V hV C 1 hs o hrow

/-- The entire signed graph constraint, in matrix coordinates, forces the
entry equation used in column_containment. -/
def matrixGraph {d : ℕ} (o j : Fin d) (V : Op) (eps : Bool) : Matrix (Fin d) (Fin d) Op :=
  (1/2:ℂ) • (Matrix.single o o (1:Op)+Matrix.single j j (1:Op)+
    sign eps • (Matrix.single j o V+Matrix.single o j (star V)))

theorem graph_entry_equation {d : ℕ} (o j : Fin d) (hjo : j≠o) (V : Op)
    (C : Matrix (Fin d) (Fin d) Op) (bit : Bool)
    (hz : C*matrixGraph o j V (!bit)=0) (i : Fin d) :
    C i j*V=sign bit • C i o := by
  have he := congrArg (fun M : Matrix (Fin d) (Fin d) Op => M i o) hz
  have hscale (z : ℂ) (M : Matrix (Fin d) (Fin d) Op) :
      (C*(z • M)) i o=z • (C*M) i o := by
    simp only [Matrix.mul_apply,Matrix.smul_apply,mul_smul_comm,← Finset.smul_sum]
  dsimp only [matrixGraph] at he
  rw [hscale] at he
  simp only [Matrix.mul_add,Matrix.add_apply] at he
  rw [hscale] at he
  simp only [Matrix.mul_add,Matrix.add_apply,Matrix.mul_single_apply_same,
    Matrix.mul_single_apply_of_ne (1:Op) j j i o (Ne.symm hjo) C,
    Matrix.mul_single_apply_of_ne (star V) o j i o (Ne.symm hjo) C,
    mul_one,add_zero,Matrix.zero_apply] at he
  have hh : C i o+sign (!bit) • (C i j*V)=0 := by
    calc
      _ = (2:ℂ) • ((1/2:ℂ) • (C i o+sign (!bit) • (C i j*V))) := by module
      _ = (2:ℂ) • (0:Op) := congrArg (fun A : Op => (2:ℂ) • A) he
      _ = 0 := by module
  cases bit
  · norm_num only [Bool.not_false,sign,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,
      one_smul,neg_one_smul] at hh ⊢
    have hh' : C i o-C i j*V=0 := by
      calc
        _ = C i o+(-1:ℂ) • (C i j*V) := by module
        _ = 0 := hh
    exact (sub_eq_zero.mp hh').symm
  · norm_num only [Bool.not_true,sign,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false,
      one_smul,neg_one_smul] at hh ⊢
    calc
      C i j*V = -C i o := eq_neg_of_add_eq_zero_right hh
      _ = (-1:ℂ) • C i o := by module

/-- The synchronized finite measurement is determined by its total and all
forbidden graph pairs. A support total A is allowed, so no faithfulness on the
ambient Hilbert space is required. -/
theorem column_unique_of_graphs (n : ℕ) (V : Fin (2^n) → Op)
    (hV : ∀ j,Unitary (V j)) (C : Fin (2^n) → Matrix (Fin (2^n)) (Fin (2^n)) Op)
    (A : Matrix (Fin (2^n)) (Fin (2^n)) Op) (hs : ∑ t,C t=A)
    (o : Fin (2^n)) (ho : o.val=0) (h0 : V o=1)
    (hz : ∀ t j,j≠o → C t*matrixGraph o j (V j) (!(parity n t.val j.val))=0) :
    ∀ t,C t=A*column n V t := by
  apply column_unique_total n V hV C A hs o
  intro t i j
  by_cases hjo : j=o
  · subst j
    rw [h0,mul_one]
    have hp : parity n t.val o.val=false := by
      rw [ho,parity_symm,RowParity.parity_zero]
    rw [hp]
    norm_num [sign]
  · exact graph_entry_equation o j hjo (V j) (C t) _ (hz t j hjo) i

/-- Once the actual supported effects have been put in these coordinates,
zero-column/reference rejection gives the signed row sum, without commutation. -/
theorem column_reference_sum (n : ℕ) (V : Fin (2^n) → Op)
    (hV : ∀ j,star (V j)=V j) (o : Fin (2^n)) (ho : o.val=0) (h0 : V o=1)
    (hz : column n V o*column n (fun _ => (1:Op)) o=0) : ∑ j,V j=0 := by
  let c : ℂ := 1/((2^n:ℕ):ℂ)
  have he := congrArg (fun M : Matrix (Fin (2^n)) (Fin (2^n)) Op => M o o) hz
  simp only [Matrix.mul_apply,column,ho,RowParity.parity_zero,sign,Bool.false_eq_true,
    ite_false,mul_one,star_one,h0,one_mul,Matrix.zero_apply,hV,
    smul_mul_smul_comm] at he
  change (∑ j,(c*c) • V j)=0 at he
  rw [← Finset.smul_sum] at he
  have hn : ((2^n:ℕ):ℂ)≠0 := by exact_mod_cast (Nat.ne_of_gt (Nat.two_pow_pos n))
  have hc : c*c≠0 := by dsimp [c]; exact mul_ne_zero (one_div_ne_zero hn) (one_div_ne_zero hn)
  exact (smul_eq_zero.mp he).resolve_left hc

#print axioms column_containment
#print axioms column_unique_total
#print axioms column_unique
#print axioms column_unique_of_graphs
#print axioms graph_entry_equation
#print axioms column_reference_sum
end Sigma2.RowWalsh
