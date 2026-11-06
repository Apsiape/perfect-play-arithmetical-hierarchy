import Sigma2.ReductionWitnessArithmetic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.Normed.Ring.Finite

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 300000
set_option pp.proofs false
namespace Sigma2.ReductionFiniteWeyl

variable (q : ℕ) [NeZero q]

def shift : Matrix (ZMod q) (ZMod q) ℂ :=
  (Equiv.addRight (1 : ZMod q)).permMatrix ℂ

def phase (ζ : ℂ) : Matrix (ZMod q) (ZMod q) ℂ :=
  Matrix.diagonal (fun i => ζ^i.val)

theorem shift_unitary : star (shift q)*shift q=1 ∧ shift q*star (shift q)=1 := by
  change (shift q).conjTranspose*shift q=1 ∧ shift q*(shift q).conjTranspose=1
  simp only [shift,Matrix.conjTranspose_permMatrix,← Matrix.permMatrix_mul,
    mul_inv_cancel,inv_mul_cancel,Matrix.permMatrix_one,and_self]

theorem phase_unitary (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q) :
    star (phase q ζ)*phase q ζ=1 ∧ phase q ζ*star (phase q ζ)=1 := by
  have hn : ‖ζ‖=1 := (hζ.isOfFinOrder (NeZero.ne q)).norm_eq_one
  have hc (i : ZMod q) : star (ζ^i.val)*ζ^i.val=1 := by
    rw [Complex.star_def,Complex.conj_mul',norm_pow,hn,one_pow]
    norm_num
  have hc' (i : ZMod q) : ζ^i.val*star (ζ^i.val)=1 := by rw [mul_comm]; exact hc i
  constructor
  · change (phase q ζ).conjTranspose*phase q ζ=1
    simp only [phase,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    change (Matrix.diagonal (fun i : ZMod q => star (ζ^i.val)*ζ^i.val))=1
    simpa only [hc] using (Matrix.diagonal_one : (Matrix.diagonal (fun _ : ZMod q => (1:ℂ)))=1)
  · change phase q ζ*(phase q ζ).conjTranspose=1
    simp only [phase,Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal]
    change (Matrix.diagonal (fun i : ZMod q => ζ^i.val*star (ζ^i.val)))=1
    simpa only [hc'] using (Matrix.diagonal_one : (Matrix.diagonal (fun _ : ZMod q => (1:ℂ)))=1)

theorem successor_phase (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q) (i : ZMod q) :
    ζ^((i+1).val)=ζ*ζ^i.val := by
  rw [ZMod.val_add,ZMod.val_one_eq_one_mod]
  rw [Nat.add_mod_mod,← Sigma2.PrimePhase.power_mod ζ q hζ.pow_eq_one (i.val+1),pow_succ,mul_comm]

theorem shift_entry (i j : ZMod q) :
    shift q i j=if i+1=j then 1 else 0 := by
  simp [shift,Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,eq_comm]

theorem weyl (ζ : ℂ) (hζ : IsPrimitiveRoot ζ q) :
    shift q*phase q ζ=ζ • (phase q ζ*shift q) := by
  apply Matrix.ext
  intro i j
  simp only [phase,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.smul_apply,smul_eq_mul]
  rw [shift_entry]
  by_cases hij : i+1=j
  · subst j
    simpa using successor_phase q ζ hζ i
  · simp [hij]

#print axioms shift_unitary
#print axioms phase_unitary
#print axioms successor_phase
#print axioms weyl
end Sigma2.ReductionFiniteWeyl
