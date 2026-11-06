import Sigma2.RowCompletenessPartitions
import Sigma2.RowPairCosets

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open RowGame RowColumns RowWalsh FiniteAncilla

variable {d : ℕ}

/-- The complete computational-basis partition in the common register. -/
def diagonalPartition (d : ℕ) : Partition (Matrix (Fin d) (Fin d) Op) (Fin d) where
  effect r := Matrix.diagonal (fun i => if i=r then (1:Op) else 0)
  selfadjoint r := by
    apply Matrix.ext
    intro i j
    by_cases hij : i=j
    · subst j
      simp only [Matrix.star_apply,Matrix.diagonal_apply_eq]
      split_ifs <;> simp
    · simp [Matrix.star_apply,Matrix.diagonal_apply,hij,Ne.symm hij]
  product r t := by
    rw [Matrix.diagonal_mul_diagonal]
    by_cases hrt : r=t
    · subst t
      rw [ite_eq_left rfl]
      apply Matrix.ext
      intro i j
      by_cases hij : i=j <;> by_cases hir : i=r <;> simp_all [Matrix.diagonal_apply,smul_zero,star_zero]
    · rw [ite_eq_right hrt]
      apply Matrix.ext
      intro i j
      by_cases hij : i=j <;> by_cases hir : i=r <;> by_cases hit : i=t <;>
        simp_all [Matrix.diagonal_apply,smul_zero,star_zero]
  total := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.sum_apply,Matrix.diagonal_apply]
    by_cases hij : i=j
    · subst j; simp
    · simp [hij,Ne.symm hij,Matrix.one_apply]

/-- Coarse computational events are the diagonal indicator of their label fiber. -/
theorem diagonal_coarse {κ : Type} [Fintype κ] [DecidableEq κ]
    (f : Fin d → κ) (k : κ) :
    ((diagonalPartition d).coarse f).effect k=
      Matrix.diagonal (fun i => if f i=k then (1:Op) else 0) := by
  apply Matrix.ext
  intro i j
  change (∑ r,if f r=k then Matrix.diagonal (fun l => if l=r then (1:Op) else 0) else 0) i j=_
  rw [Matrix.sum_apply,Finset.sum_eq_single i]
  · by_cases hi : f i=k
    · rw [ite_eq_left hi]; simp [Matrix.diagonal_apply,hi]
    · rw [ite_eq_right hi]; simp [Matrix.diagonal_apply,hi]
  · intro r hr hri
    by_cases hfr : f r=k
    · rw [ite_eq_left hfr]; simp [Matrix.diagonal_apply,Ne.symm hri]
    · rw [ite_eq_right hfr]; rfl
  · simp

/-- A permutation matrix over the original operator identity. -/
def permutationMatrix (e : Equiv.Perm (Fin d)) : Matrix (Fin d) (Fin d) Op :=
  Matrix.of (fun i j => if j=e i then 1 else 0)

theorem permutation_left (e : Equiv.Perm (Fin d)) (M : Matrix (Fin d) (Fin d) Op) (i j : Fin d) :
    (permutationMatrix e*M) i j=M (e i) j := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (e i)]
  · simp [permutationMatrix]
  · intro k hk hki; simp [permutationMatrix,hki]
  · simp

theorem permutation_right (e : Equiv.Perm (Fin d)) (M : Matrix (Fin d) (Fin d) Op) (i j : Fin d) :
    (M*permutationMatrix e) i j=M i (e.symm j) := by
  rw [Matrix.mul_apply,Finset.sum_eq_single (e.symm j)]
  · simp [permutationMatrix]
  · intro k hk hki
    have hne : j≠e k := by
      intro he
      apply hki
      apply e.injective
      simpa using he.symm
    simp [permutationMatrix,hne]
  · simp

theorem permutation_star (e : Equiv.Perm (Fin d)) :
    star (permutationMatrix e)=permutationMatrix e.symm := by
  apply Matrix.ext
  intro i j
  change star (if i=e j then (1:Op) else 0)=(if j=e.symm i then (1:Op) else 0)
  have he : i=e j ↔ j=e.symm i := by constructor <;> intro h <;> simp [h]
  by_cases hi : i=e j
  · have hj := he.mp hi
    simp only [ite_eq_left hi,ite_eq_left hj]
    exact star_one Op
  · have hj : ¬j=e.symm i := fun h => hi (he.mpr h)
    simp only [ite_eq_right hi,ite_eq_right hj]
    exact star_zero Op

/-- The involutive bitwise shift, in precisely the frozen numerical coordinates. -/
def shift (n j : ℕ) (hj : j<2^n) : Matrix (Fin (2^n)) (Fin (2^n)) Op :=
  permutationMatrix (xorEquiv n j hj)

theorem xorEquiv_symm (n j : ℕ) (hj : j<2^n) :
    (xorEquiv n j hj).symm=xorEquiv n j hj := by rfl

theorem shift_star (n j : ℕ) (hj : j<2^n) : star (shift n j hj)=shift n j hj := by
  exact (permutation_star _).trans (congrArg permutationMatrix (xorEquiv_symm n j hj))

theorem shift_square (n j : ℕ) (hj : j<2^n) : shift n j hj*shift n j hj=1 := by
  unfold shift
  apply Matrix.ext
  intro i k
  rw [permutation_left]
  change (if k=(xorEquiv n j hj) ((xorEquiv n j hj) i) then (1:Op) else 0)=_
  have he : (xorEquiv n j hj) ((xorEquiv n j hj) i)=i :=
    (xorEquiv n j hj).left_inv i
  rw [he]
  simp [Matrix.one_apply,eq_comm]

/-- Canonical two-point coset label; zero coset is always represented by zero. -/
def cosetLabel (n j : ℕ) (hj : j<2^n) (i : Fin (2^n)) : Fin (2^n) :=
  if i.val ≤ Nat.xor i.val j then i else (xorEquiv n j hj) i

theorem cosetLabel_shift (n j : ℕ) (hj : j<2^n) (i : Fin (2^n)) :
    cosetLabel n j hj ((xorEquiv n j hj) i)=cosetLabel n j hj i := by
  have he : Nat.xor (Nat.xor i.val j) j=i.val := by simp [Nat.xor_eq]
  by_cases hi : i.val ≤ Nat.xor i.val j
  · by_cases hh : Nat.xor i.val j ≤ i.val
    · have hi' : (xorEquiv n j hj) i=i := Fin.ext (by change Nat.xor i.val j=i.val; omega)
      rw [hi']
    · simp only [cosetLabel,show ((xorEquiv n j hj) i).val=Nat.xor i.val j from rfl,he,
        hi,hh,ite_true,ite_false]
      exact (xorEquiv n j hj).left_inv i
  · have hh : Nat.xor i.val j ≤ i.val := by omega
    simp only [cosetLabel,show ((xorEquiv n j hj) i).val=Nat.xor i.val j from rfl,he,
      hi,hh,ite_true,ite_false]

theorem cosetLabel_canonical (n j : ℕ) (hj : j<2^n) (i : Fin (2^n)) :
    (cosetLabel n j hj i).val ≤ Nat.xor (cosetLabel n j hj i).val j := by
  unfold cosetLabel
  split_ifs with hi
  · exact hi
  · change Nat.xor i.val j ≤ Nat.xor (Nat.xor i.val j) j
    rw [show Nat.xor (Nat.xor i.val j) j=i.val from by simp [Nat.xor_eq]]
    omega

/-- Noncanonical cosets are genuine zero outcomes in the complete partition. -/
theorem coset_noncanonical (n j : ℕ) (hj : j<2^n) (r : Fin (2^n))
    (hr : ¬r.val ≤ Nat.xor r.val j) :
    ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect r=0 := by
  apply Partition.coarse_outside
  intro i he
  have hh := cosetLabel_canonical n j hj i
  rw [he] at hh
  exact hr hh

/-- Each complete diagonal coset commutes with the shift through that coset. -/
theorem shift_coset_commute (n j : ℕ) (hj : j<2^n) (r : Fin (2^n)) :
    shift n j hj*((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect r=
      ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect r*shift n j hj := by
  unfold shift
  rw [diagonal_coarse]
  apply Matrix.ext
  intro i k
  rw [permutation_left,permutation_right]
  simp only [Matrix.diagonal_apply]
  have he : (xorEquiv n j hj) i=k ↔ i=(xorEquiv n j hj).symm k := by
    constructor
    · intro h; apply (xorEquiv n j hj).injective; simpa using h
    · intro h; simpa using congrArg (xorEquiv n j hj) h
  by_cases hik : (xorEquiv n j hj) i=k
  · subst k
    simp [Equiv.symm_apply_apply,cosetLabel_shift]
  · simp [hik,he.not.mp hik]

/-- Complex scalar multiplication preserves matrix commutation. -/
theorem matrix_commute_smul {d : ℕ} (M N : Matrix (Fin d) (Fin d) Op)
    (h : M*N=N*M) (c : ℂ) : M*(c • N)=(c • N)*M := by
  calc
    M*(c • N)=c • (M*N) := Matrix.mul_smul M c N
    _ = c • (N*M) := congrArg (fun A : Matrix (Fin d) (Fin d) Op => c • A) h
    _ = (c • N)*M := (Matrix.smul_mul c N M).symm

/-- The scalar-pair PVM, obtained from its shift sign and canonical Z coset.
All cosets are present simultaneously; no incomplete zero-coset family is used. -/
def pairPartition (n j : ℕ) (hj : j<2^n) :
    Partition (Matrix (Fin (2^n)) (Fin (2^n)) Op) (Bool × Fin (2^n)) :=
  (Partition.reflection (shift n j hj) (shift_star n j hj) (shift_square n j hj)).joint
    ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)) (by
      intro b r
      let D := ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect r
      have hs : Commute D (shift n j hj) := (shift_coset_commute n j hj r).symm
      have hc : Commute D (sign b • shift n j hj) := matrix_commute_smul _ _ hs.eq _
      have ha : Commute D (1+sign b • shift n j hj) := (Commute.one_right D).add_right hc
      exact (matrix_commute_smul _ _ ha.eq (1/2:ℂ)).symm)

theorem pair_noncanonical (n j : ℕ) (hj : j<2^n) (a : Bool × Fin (2^n))
    (ha : ¬a.2.val ≤ Nat.xor a.2.val j) : (pairPartition n j hj).effect a=0 := by
  change (Partition.reflection _ _ _).effect a.1*
    ((diagonalPartition (2^n)).coarse (cosetLabel n j hj)).effect a.2=0
  rw [coset_noncanonical n j hj a.2 ha,mul_zero]

/-- Complete global X outcomes in the same numerical register. -/
def fourierPartition (n : ℕ) : Partition (Matrix (Fin (2^n)) (Fin (2^n)) Op) (Fin (2^n)) where
  effect t := column n (fun _ => (1:Op)) t
  selfadjoint t := column_star _ _ _
  product t u := by
    by_cases h : t=u
    · subst u
      rw [if_pos rfl]
      exact column_idempotent (Nat.two_pow_pos n) n _ (fun _ => ⟨by simp,by simp⟩) t
    · rw [if_neg h]
      exact column_mul_ne n _ (fun _ => ⟨by simp,by simp⟩) t u h
  total := column_sum n _ (fun _ => ⟨by simp,by simp⟩)

/-- Fourier outcomes have the exact frozen parity eigenvalue under every shift. -/
theorem shift_fourier (n j : ℕ) (hj : j<2^n) (t : Fin (2^n)) :
    shift n j hj*(fourierPartition n).effect t=
      sign (parity n j t.val) • (fourierPartition n).effect t := by
  unfold shift
  apply Matrix.ext
  intro i k
  rw [permutation_left]
  change ((1/((2^n:ℕ):ℂ))*sign (parity n t.val (Nat.xor i.val j))*
    sign (parity n t.val k.val)) • ((1:Op)*star (1:Op)) =
    sign (parity n j t.val) •
      (((1/((2^n:ℕ):ℂ))*sign (parity n t.val i.val)*sign (parity n t.val k.val)) •
        ((1:Op)*star (1:Op)))
  rw [RowScalar.parity_right_xor,sign_xor,parity_symm n t.val j,smul_smul]
  congr 1
  ring

/-- A real diagonal Walsh character. -/
def phase (n j : ℕ) : Matrix (Fin (2^n)) (Fin (2^n)) Op :=
  Matrix.diagonal (fun i => sign (parity n j i.val) • (1:Op))

theorem phase_star (n j : ℕ) : star (phase n j)=phase n j := by
  apply Matrix.ext
  intro i k
  by_cases hik : i=k
  · subst k
    simp [phase,Matrix.star_apply,Matrix.diagonal_apply,sign_star]
  · simp only [phase,Matrix.star_apply,Matrix.diagonal_apply,ite_eq_right hik,ite_eq_right (Ne.symm hik)]
    exact star_zero Op

theorem phase_square (n j : ℕ) : phase n j*phase n j=1 := by
  rw [phase,Matrix.diagonal_mul_diagonal]
  have he : (fun i : Fin (2^n) =>
      (sign (parity n j i.val) • (1:Op))*(sign (parity n j i.val) • (1:Op)))=fun _ => (1:Op) := by
    funext i
    rw [smul_mul_smul_comm,sign_sq,mul_one,one_smul]
  rw [he,Matrix.diagonal_one]

theorem phase_diagonal (n j : ℕ) (r : Fin (2^n)) :
    phase n j*(diagonalPartition (2^n)).effect r=
      sign (parity n j r.val) • (diagonalPartition (2^n)).effect r := by
  rw [phase,diagonalPartition,Matrix.diagonal_mul_diagonal]
  apply Matrix.ext
  intro i k
  by_cases hik : i=k <;> by_cases hir : i=r <;>
    simp_all [Matrix.diagonal_apply,smul_zero,star_zero]
  all_goals module

/-- The exact finite Pauli commutation law for arbitrary bounded bit masks. -/
theorem shift_phase (n j m : ℕ) (hj : j<2^n) :
    shift n j hj*phase n m=sign (parity n m j) • (phase n m*shift n j hj) := by
  unfold shift
  apply Matrix.ext
  intro i k
  rw [permutation_left]
  change (phase n m) ((xorEquiv n j hj) i) k=
    sign (parity n m j) • ((phase n m*permutationMatrix (xorEquiv n j hj)) i k)
  rw [permutation_right]
  by_cases hk : k=(xorEquiv n j hj) i
  · subst k
    simp only [phase,Matrix.diagonal_apply_eq,Equiv.symm_apply_apply]
    change sign (parity n m (Nat.xor i.val j)) • (1:Op)=
      sign (parity n m j) • (sign (parity n m i.val) • (1:Op))
    rw [RowScalar.parity_right_xor,sign_xor,smul_smul,mul_comm]
  · have hi : i≠(xorEquiv n j hj).symm k := by
      intro he
      apply hk
      simpa using (congrArg (xorEquiv n j hj) he).symm
    simp [phase,Matrix.diagonal_apply,Ne.symm hk,hi]
    module

theorem shift_commute (n j k : ℕ) (hj : j<2^n) (hk : k<2^n) :
    shift n j hj*shift n k hk=shift n k hk*shift n j hj := by
  unfold shift
  apply Matrix.ext
  intro i l
  rw [permutation_left,permutation_left]
  have he : (xorEquiv n k hk) ((xorEquiv n j hj) i)=
      (xorEquiv n j hj) ((xorEquiv n k hk) i) := by
    apply Fin.ext
    change Nat.xor (Nat.xor i.val j) k=Nat.xor (Nat.xor i.val k) j
    simp only [Nat.xor_eq]
    rw [Nat.xor_assoc,Nat.xor_comm j k,← Nat.xor_assoc]
  change (if l=(xorEquiv n k hk) ((xorEquiv n j hj) i) then (1:Op) else 0)=
    (if l=(xorEquiv n j hj) ((xorEquiv n k hk) i) then (1:Op) else 0)
  rw [he]

theorem phase_commute (n j k : ℕ) : phase n j*phase n k=phase n k*phase n j := by
  rw [phase,phase,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp only [smul_mul_smul_comm,mul_one]
  rw [mul_comm]

/-- The genuine l2 shift and phase operators in a common finite register. -/
def scalarX (n : ℕ) (k : Fin n) : Op :=
  matrixOp (2^n) (shift n (2^k.val) (Nat.pow_lt_pow_right (by decide) k.isLt))

def scalarZ (n : ℕ) (k : Fin n) : Op := matrixOp (2^n) (phase n (2^k.val))

theorem scalarX_star (n : ℕ) (k : Fin n) : star (scalarX n k)=scalarX n k := by
  rw [scalarX,← matrixOp_star,shift_star]

theorem scalarZ_star (n : ℕ) (k : Fin n) : star (scalarZ n k)=scalarZ n k := by
  rw [scalarZ,← matrixOp_star,phase_star]

theorem scalarX_square (n : ℕ) (k : Fin n) : scalarX n k*scalarX n k=1 := by
  rw [scalarX,← matrixOp_mul,shift_square,matrixOp_one]

theorem scalarZ_square (n : ℕ) (k : Fin n) : scalarZ n k*scalarZ n k=1 := by
  rw [scalarZ,← matrixOp_mul,phase_square,matrixOp_one]

theorem scalarX_commute (n : ℕ) (k l : Fin n) : Commute (scalarX n k) (scalarX n l) := by
  change matrixOp _ _*matrixOp _ _=matrixOp _ _*matrixOp _ _
  rw [← matrixOp_mul,← matrixOp_mul,shift_commute]

theorem scalarZ_commute (n : ℕ) (k l : Fin n) : Commute (scalarZ n k) (scalarZ n l) := by
  change matrixOp _ _*matrixOp _ _=matrixOp _ _*matrixOp _ _
  rw [← matrixOp_mul,← matrixOp_mul,phase_commute]

theorem scalarXZ_commute (n : ℕ) (k l : Fin n) (h : k≠l) :
    Commute (scalarX n k) (scalarZ n l) := by
  have hkl : l.val≠k.val := by intro he; exact h (Fin.ext he.symm)
  change matrixOp _ _*matrixOp _ _=matrixOp _ _*matrixOp _ _
  rw [← matrixOp_mul,← matrixOp_mul,shift_phase,
    RowParity.parity_single n l.val _ l.isLt,Nat.testBit_two_pow_of_ne (by omega),
    ]
  simp [sign]

theorem scalarXZ_anticommute (n : ℕ) (k : Fin n) :
    scalarX n k*scalarZ n k= -(scalarZ n k*scalarX n k) := by
  change matrixOp _ _*matrixOp _ _= -(matrixOp _ _*matrixOp _ _)
  rw [← matrixOp_mul,← matrixOp_mul,shift_phase,
    RowParity.parity_single n k.val _ k.isLt,(show Nat.testBit (2^k.val) k.val=true from by simp)]
  change matrixOp _ ((-1:ℂ) • _) = -matrixOp _ _
  rw [matrixOp_smul]
  exact neg_one_smul ℂ (matrixOp (2^n) (phase n (2^k.val)*shift n (2^k.val) _))

theorem scalar_pauli (n : ℕ) (k l : Fin n) (h : k≠l) :
    FourUnits.TwoPairs 1 (scalarX n k) (scalarZ n k) (scalarX n l) (scalarZ n l) := by
  have hp (k : Fin n) : PauliMatrixUnits.Pair 1 (scalarX n k) (scalarZ n k) :=
    ⟨⟨by simp,by simp⟩,scalarX_star n k,scalarZ_star n k,
      by simp,by simp,by simp,by simp,scalarX_square n k,scalarZ_square n k,
      scalarXZ_anticommute n k⟩
  exact ⟨hp k,hp l,scalarX_commute n k l,scalarXZ_commute n k l h,
    (scalarXZ_commute n l k (Ne.symm h)).symm,scalarZ_commute n k l⟩

/-- An old local operator tensored with the scalar identity, as actual blocks. -/
def constantDiagonal (E : Op) : Matrix (Fin d) (Fin d) Op := Matrix.diagonal (fun _ => E)

theorem constantDiagonal_projection (E : Op) (hE : Projection E) :
    star (constantDiagonal (d:=d) E)=constantDiagonal (d:=d) E ∧
      constantDiagonal (d:=d) E*constantDiagonal (d:=d) E=constantDiagonal (d:=d) E := by
  constructor
  · apply Matrix.ext
    intro i j
    by_cases hij : i=j
    · subst j; simp [constantDiagonal,Matrix.star_apply,hE.1]
    · simp only [constantDiagonal,Matrix.star_apply,Matrix.diagonal_apply,ite_eq_right hij,ite_eq_right (Ne.symm hij)]
      exact star_zero Op
  · rw [constantDiagonal,Matrix.diagonal_mul_diagonal]
    simp only [hE.2]

/-- Scalar blocks commute with every old operator; this is independent of the state. -/
def ScalarBlocks (M : Matrix (Fin d) (Fin d) Op) : Prop := ∀ E : Op,Commute (constantDiagonal E) M

theorem scalar_diagonal (r : Fin d) : ScalarBlocks ((diagonalPartition d).effect r) := by
  intro E
  change constantDiagonal E*(diagonalPartition d).effect r=
    (diagonalPartition d).effect r*constantDiagonal E
  rw [constantDiagonal,diagonalPartition,Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem scalar_shift (n j : ℕ) (hj : j<2^n) : ScalarBlocks (shift n j hj) := by
  unfold shift
  intro E
  change constantDiagonal E*shift n j hj=shift n j hj*constantDiagonal E
  unfold shift
  apply Matrix.ext
  intro i k
  rw [permutation_right,permutation_left]
  change (Matrix.diagonal (fun _ => E)) i ((xorEquiv n j hj).symm k)=
    (Matrix.diagonal (fun _ => E)) ((xorEquiv n j hj) i) k
  have he : i=(xorEquiv n j hj).symm k ↔ (xorEquiv n j hj) i=k := by
    constructor
    · intro h; simpa using congrArg (xorEquiv n j hj) h
    · intro h; apply (xorEquiv n j hj).injective; simpa using h
  simp only [Matrix.diagonal_apply,he]

theorem scalar_coarse {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Partition (Matrix (Fin d) (Fin d) Op) ι) (hP : ∀ i,ScalarBlocks (P.effect i)) (f : ι → κ) (k : κ) :
    ScalarBlocks ((P.coarse f).effect k) := by
  intro E
  apply Commute.sum_right
  intro i hi
  change Commute (constantDiagonal E) (if f i=k then P.effect i else 0)
  split_ifs
  · exact hP i E
  · exact Commute.zero_right _

theorem scalar_pair (n j : ℕ) (hj : j<2^n) (a : Bool × Fin (2^n)) :
    ScalarBlocks ((pairPartition n j hj).effect a) := by
  intro E
  apply Commute.mul_right
  · have hs := scalar_shift n j hj E
    have hc : Commute (constantDiagonal E) (sign a.1 • shift n j hj) :=
      matrix_commute_smul _ _ hs.eq _
    have ha := (Commute.one_right (constantDiagonal E)).add_right hc
    exact matrix_commute_smul _ _ ha.eq (1/2:ℂ)
  · exact scalar_coarse (diagonalPartition _) scalar_diagonal (cosetLabel n j hj) a.2 E

/-- The three scalar classes used by every slot, from the same complete pair PVM. -/
def pairClass {n : ℕ} (a : Bool × Fin (2^n)) : Fin 3 :=
  if a.2.val=0 then ⟨if a.1 then 1 else 0,by split <;> omega⟩ else 2

/-- Simultaneous honest slot POVM: old binary event times the scalar three-class PVM. -/
def slotPartition (n j : ℕ) (hj : j<2^n) (E : Op) (hE : Projection E) :
    Partition (Matrix (Fin (2^n)) (Fin (2^n)) Op) (Bool × Fin 3) :=
  let h := constantDiagonal_projection (d:=2^n) E hE
  (Partition.binary (constantDiagonal E) h.1 h.2).joint
    ((pairPartition n j hj).coarse pairClass) (by
      intro b c
      have hc := scalar_coarse (pairPartition n j hj) (scalar_pair n j hj) pairClass c E
      cases b
      · exact (Commute.one_left _).sub_left hc |>.eq
      · exact hc.eq)

end Sigma2.RowCompleteness
