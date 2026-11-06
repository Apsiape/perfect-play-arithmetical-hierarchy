import Sigma2.RowCompletenessFamily

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns RowWalsh FiniteAncilla TensorLifts

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩


/-- Linear spectral effects inherit a reflection's vector mirror. -/
theorem reflection_mirror (U V : Op) (hsU : star U=U) (hsV : star V=V)
    (hqU : U*U=1) (hqV : V*V=1) (v : AB) (hm : left U v=right V v) (b : Bool) :
    left ((Partition.reflection U hsU hqU).effect b) v=
      right ((Partition.reflection V hsV hqV).effect b) v := by
  change left ((1/2:ℂ) • (1+sign b • U)) v=right ((1/2:ℂ) • (1+sign b • V)) v
  rw [MagicRelations.left_smul,MagicRelations.right_smul,DiagonalIdentification.left_add,
    DiagonalIdentification.right_add,MagicRelations.left_smul,MagicRelations.right_smul,left_one,right_one]
  change (1/2:ℂ) • (v+sign b • left U v)=(1/2:ℂ) • (v+sign b • right V v)
  rw [hm]

/-- Every numerical shift is a real symmetric operator on the finite register. -/
theorem shift_mirror (n j : ℕ) (hj : j<2^n) (v : AB) :
    left (matrixOp (2^n) (shift n j hj)) (entangle (2^n) v)=
      right (matrixOp (2^n) (shift n j hj)) (entangle (2^n) v) := by
  apply matrix_mirror
  intro i k
  have hi : (xorEquiv n j hj) ((xorEquiv n j hj) i)=i := (xorEquiv n j hj).left_inv i
  have hk : (xorEquiv n j hj) ((xorEquiv n j hj) k)=k := (xorEquiv n j hj).left_inv k
  have he : k=(xorEquiv n j hj) i ↔ i=(xorEquiv n j hj) k := by
    constructor
    · intro h
      have hh := congrArg (xorEquiv n j hj) h
      rw [hi] at hh
      exact hh.symm
    · intro h
      have hh := congrArg (xorEquiv n j hj) h
      rw [hk] at hh
      exact hh.symm
  change left (if k=(xorEquiv n j hj) i then (1:Op) else 0) v=
    right (if i=(xorEquiv n j hj) k then (1:Op) else 0) v
  by_cases h : k=(xorEquiv n j hj) i
  · simp only [ite_eq_left h,ite_eq_left (he.mp h),left_one,right_one]
  · have h' : ¬i=(xorEquiv n j hj) k := fun hh => h (he.mpr hh)
    simp only [ite_eq_right h,ite_eq_right h',CoarseCells.left_zero,CoarseCells.right_zero]

/-- The phase mirror has the same real sign on both sides of each diagonal block. -/
theorem phase_mirror (n j : ℕ) (v : AB) :
    left (matrixOp (2^n) (phase n j)) (entangle (2^n) v)=
      right (matrixOp (2^n) (phase n j)) (entangle (2^n) v) := by
  apply matrix_mirror
  intro i k
  by_cases hik : i=k
  · subst k
    simp only [phase,Matrix.diagonal_apply_eq,MagicRelations.left_smul,MagicRelations.right_smul,
      left_one,right_one]
  · simp [phase,Matrix.diagonal_apply,hik,Ne.symm hik]

theorem scalarX_mirror (n : ℕ) (k : Fin n) (v : AB) :
    left (scalarX n k) (entangle (2^n) v)=right (scalarX n k) (entangle (2^n) v) :=
  shift_mirror n _ _ v

theorem scalarZ_mirror (n : ℕ) (k : Fin n) (v : AB) :
    left (scalarZ n k) (entangle (2^n) v)=right (scalarZ n k) (entangle (2^n) v) :=
  phase_mirror n _ v

/-- Computational fine outcomes synchronize on the same finite entangled register. -/
theorem diagonal_mirror (d : ℕ) [NeZero d] (r : Fin d) (v : AB) :
    left ((realizePartition (diagonalPartition d)).effect r) (entangle d v)=
      right ((realizePartition (diagonalPartition d)).effect r) (entangle d v) := by
  apply matrix_mirror
  intro i j
  by_cases hij : i=j
  · subst j
    simp only [diagonalPartition,Matrix.diagonal_apply_eq]
    split_ifs <;> simp
  · simp [diagonalPartition,Matrix.diagonal_apply,hij,Ne.symm hij]

/-- Coarse matrix partitions are realized by the same finite operator sums. -/
theorem realize_coarse {d : ℕ} [NeZero d] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Partition (Matrix (Fin d) (Fin d) Op) ι) (f : ι → κ) (k : κ) :
    (realizePartition (P.coarse f)).effect k=((realizePartition P).coarse f).effect k := by
  change matrixOp d (∑ i,if f i=k then P.effect i else 0)=
    ∑ i,if f i=k then matrixOp d (P.effect i) else 0
  rw [matrixOp_sum]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

/-- Each raw operator-matrix joint is the product of its realized effects. -/
theorem realize_joint {d : ℕ} [NeZero d] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P : Partition (Matrix (Fin d) (Fin d) Op) ι) (Q : Partition (Matrix (Fin d) (Fin d) Op) κ)
    (hc : ∀ i j,P.effect i*Q.effect j=Q.effect j*P.effect i) (ij : ι × κ) :
    (realizePartition (P.joint Q hc)).effect ij=
      (realizePartition P).effect ij.1*(realizePartition Q).effect ij.2 := by
  exact matrixOp_mul _ _ _

/-- Matrix-level joint mirrors become the exact l2 mirrors, with reversed Bob order. -/
theorem realize_joint_mirror {d : ℕ} [NeZero d] {ι κ : Type}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (P P' : Partition (Matrix (Fin d) (Fin d) Op) ι) (Q Q' : Partition (Matrix (Fin d) (Fin d) Op) κ)
    (hc : ∀ i j,P.effect i*Q.effect j=Q.effect j*P.effect i)
    (hc' : ∀ i j,P'.effect i*Q'.effect j=Q'.effect j*P'.effect i)
    (v : AB) (hP : ∀ i,left ((realizePartition P).effect i) v=right ((realizePartition P').effect i) v)
    (hQ : ∀ j,left ((realizePartition Q).effect j) v=right ((realizePartition Q').effect j) v)
    (a : ι × κ) :
    left ((realizePartition (P.joint Q hc)).effect a) v=
      right ((realizePartition (P'.joint Q' hc')).effect a) v := by
  rw [realize_joint,realize_joint]
  have hh := product_mirror _ _ _ _ v (hP a.1) (hQ a.2)
  have he : (realizePartition Q').effect a.2*(realizePartition P').effect a.1=
      (realizePartition P').effect a.1*(realizePartition Q').effect a.2 := by
    change matrixOp d _*matrixOp d _=matrixOp d _*matrixOp d _
    rw [← matrixOp_mul,← matrixOp_mul,← hc']
  rw [he] at hh
  exact hh

/-- Every complete scalar-pair outcome synchronizes on the common register. -/
theorem pair_mirror (n j : ℕ) (hj : j<2^n) (v : AB) (a : Bool × Fin (2^n)) :
    left ((realizePartition (pairPartition n j hj)).effect a) (entangle (2^n) v)=
      right ((realizePartition (pairPartition n j hj)).effect a) (entangle (2^n) v) := by
  unfold pairPartition
  apply realize_joint_mirror
  · intro b
    change left (matrixOp (2^n) ((1/2:ℂ) • (1+sign b • shift n j hj))) (entangle (2^n) v)=
      right (matrixOp (2^n) ((1/2:ℂ) • (1+sign b • shift n j hj))) (entangle (2^n) v)
    rw [matrixOp_smul,matrixOp_add,matrixOp_one,matrixOp_smul,
      MagicRelations.left_smul,MagicRelations.right_smul,DiagonalIdentification.left_add,
      DiagonalIdentification.right_add,MagicRelations.left_smul,MagicRelations.right_smul,left_one,right_one]
    change (1/2:ℂ) • (entangle (2^n) v+sign b • left (matrixOp (2^n) (shift n j hj)) (entangle (2^n) v))=
      (1/2:ℂ) • (entangle (2^n) v+sign b • right (matrixOp (2^n) (shift n j hj)) (entangle (2^n) v))
    rw [shift_mirror]
  · intro r
    simp only [realize_coarse]
    exact coarse_mirror _ _ _ (fun i => diagonal_mirror _ i v) _ r

theorem commuting_product_mirror (A B A' B' : Op) (v : AB)
    (hA : left A v=right A' v) (hB : left B v=right B' v) (hc : A'*B'=B'*A') :
    left (A*B) v=right (A'*B') v := by
  have hh := product_mirror A B A' B' v hA hB
  rw [← hc] at hh
  exact hh

theorem amplify_mirror (d : ℕ) [NeZero d] (E F : Op) (v : AB)
    (hm : left E v=right F v) : left (amplify d E) (entangle d v)=
      right (amplify d F) (entangle d v) := by
  rw [left_entangle,right_entangle,hm]

theorem fourier_mirror (n : ℕ) (r : Fin (2^n)) (v : AB) :
    left ((realizePartition (fourierPartition n)).effect r) (entangle (2^n) v)=
      right ((realizePartition (fourierPartition n)).effect r) (entangle (2^n) v) := by
  apply matrix_mirror
  intro i j
  let c : ℂ := 1/((2^n:ℕ):ℂ)
  let chi := fun i : Fin (2^n) => sign (parity n r.val i.val)
  change left ((c*chi i*chi j) • ((1:Op)*star (1:Op))) v=
    right ((c*chi j*chi i) • ((1:Op)*star (1:Op))) v
  have hc : c*chi i*chi j=c*chi j*chi i := by ring
  rw [hc]
  simp only [star_one,mul_one,MagicRelations.left_smul,MagicRelations.right_smul,left_one,right_one]

theorem rowAxis_mirror {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) (v : AB) :
    left (rowAxis R g k) (entangle (RowSlots.dimension R) v)=
      right (rowAxis R g k) (entangle (RowSlots.dimension R) v) := by
  simp only [RowScalar.dimension_bits]
  by_cases hk : k.val<2
  · simpa only [rowAxis,ite_eq_left hk] using scalarZ_mirror (bits R) (axisBit R g k) v
  · simpa only [rowAxis,ite_eq_right hk] using scalarX_mirror (bits R) (axisBit R g k) v

/-- Every real magic-square cell synchronizes on the same ancillary state. -/
theorem rowMagic_mirror {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (x y : Fin 3) (v : AB) :
    left (rowMagic R g x y) (entangle (RowSlots.dimension R) v)=
      right (rowMagic R g x y) (entangle (RowSlots.dimension R) v) := by
  simp only [RowScalar.dimension_bits]
  let w := entangle (2^(bits R)) v
  have hX0 := scalarX_mirror (bits R) (squareBit R g 0) v
  have hZ0 := scalarZ_mirror (bits R) (squareBit R g 0) v
  have hX1 := scalarX_mirror (bits R) (squareBit R g 1) v
  have hZ1 := scalarZ_mirror (bits R) (squareBit R g 1) v
  have hrel := rowMagic_relations R g
  have h02 := commuting_product_mirror _ _ _ _ w hZ0 hX1 (hrel.row_commute 0 0 1)
  have h12 := commuting_product_mirror _ _ _ _ w hZ1 hX0 (hrel.row_commute 1 0 1)
  have h20 := commuting_product_mirror _ _ _ _ w hZ0 hZ1 (hrel.col_commute 0 1 0)
  have h21 := commuting_product_mirror _ _ _ _ w hX1 hX0 (hrel.col_commute 0 1 1)
  have h22 := commuting_product_mirror _ _ _ _ w h20 h21 (hrel.row_commute 2 0 1)
  fin_cases x <;> fin_cases y
  · exact hZ0
  · exact hX1
  · exact h02
  · exact hZ1
  · exact hX0
  · exact h12
  · exact h20
  · exact h21
  · exact h22

theorem padPartition_mirror {ι : Type} [Fintype ι] [DecidableEq ι]
    (P Q : Partition Op ι) (N : ℕ) (num : ι → ℕ) (hn : ∀ i,num i<N) (v : AB)
    (hm : ∀ i,left (P.effect i) v=right (Q.effect i) v) (a : Fin N) :
    left ((padPartition P N num hn).effect a) v=right ((padPartition Q N num hn).effect a) v :=
  coarse_mirror P Q v hm _ a

theorem linePartition_mirror (U V U' V' : Op)
    (hsU : star U=U) (hsV : star V=V) (hqU : U*U=1) (hqV : V*V=1) (hc : U*V=V*U)
    (hsU' : star U'=U') (hsV' : star V'=V') (hqU' : U'*U'=1) (hqV' : V'*V'=1) (hc' : U'*V'=V'*U')
    (v : AB) (hU : left U v=right U' v) (hV : left V v=right V' v) (a : Bool × Bool) :
    left ((linePartition U V hsU hsV hqU hqV hc).effect a) v=
      right ((linePartition U' V' hsU' hsV' hqU' hqV' hc').effect a) v := by
  unfold linePartition
  apply joint_mirror
  · exact reflection_mirror U U' hsU hsU' hqU hqU' v hU
  · exact reflection_mirror V V' hsV hsV' hqV hqV' v hV

/-- The honest six-outcome slot POVMs synchronize for every mirrored old event. -/
theorem slotPartition_mirror (n j : ℕ) (hj : j<2^n) (E F : Op)
    (hE : Projection E) (hF : Projection F) (v : AB) (hm : left E v=right F v)
    (a : Bool × Fin 3) :
    left ((realizePartition (slotPartition n j hj E hE)).effect a) (entangle (2^n) v)=
      right ((realizePartition (slotPartition n j hj F hF)).effect a) (entangle (2^n) v) := by
  unfold slotPartition
  apply realize_joint_mirror
  · intro b
    cases b
    · change left (matrixOp (2^n) (1-constantDiagonal E)) (entangle (2^n) v)=
        right (matrixOp (2^n) (1-constantDiagonal F)) (entangle (2^n) v)
      rw [matrixOp_sub,matrixOp_sub,matrixOp_one,matrixOp_constantDiagonal,matrixOp_constantDiagonal,
        PureSupport.left_sub,MagicRelations.right_sub,left_one,right_one]
      change entangle (2^n) v-left (amplify (2^n) E) (entangle (2^n) v)=
        entangle (2^n) v-right (amplify (2^n) F) (entangle (2^n) v)
      rw [amplify_mirror _ E F v hm]
    · change left (matrixOp (2^n) (constantDiagonal E)) (entangle (2^n) v)=
        right (matrixOp (2^n) (constantDiagonal F)) (entangle (2^n) v)
      rw [matrixOp_constantDiagonal,matrixOp_constantDiagonal]
      exact amplify_mirror _ E F v hm
  · intro c
    simp only [realize_coarse]
    exact coarse_mirror _ _ _ (pair_mirror n j hj v) _ c

theorem deterministic_mirror {ι : Type} [Fintype ι] [DecidableEq ι]
    (i₀ i : ι) (v : AB) : left ((Partition.deterministic (A:=Op) i₀).effect i) v=
      right ((Partition.deterministic (A:=Op) i₀).effect i) v := by
  change left (if i=i₀ then (1:Op) else 0) v=right (if i=i₀ then (1:Op) else 0) v
  split_ifs <;> simp

/-- Synchronization of every concrete new POVM in one shared enlarged l2 model. -/
theorem newPartition_mirror (G : Game) (R : Rows G.scenario) (E F : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (v : AB)
    (hm : ∀ i,left (E i) v=right (F i) v) (q : Q R) (a : AA (scenario G R)) :
    left ((newPartition G R E hE q).effect a) (entangle (RowSlots.dimension R) v)=
      right ((newPartition G R F hF q).effect a) (entangle (RowSlots.dimension R) v) := by
  cases q with
  | anchor => exact deterministic_mirror _ _ _
  | cell g x y =>
      apply padPartition_mirror
      intro b
      apply reflection_mirror
      exact rowMagic_mirror R g x y v
  | line g col k =>
      apply padPartition_mirror
      intro b
      apply linePartition_mirror
      · cases col
        · exact rowMagic_mirror R g k 0 v
        · exact rowMagic_mirror R g 0 k v
      · cases col
        · exact rowMagic_mirror R g k 1 v
        · exact rowMagic_mirror R g 1 k v
  | cross g h k l =>
      dsimp only [newPartition]
      split_ifs with hgh
      · exact deterministic_mirror _ _ _
      · apply padPartition_mirror
        intro b
        apply linePartition_mirror
        · exact rowAxis_mirror R g k v
        · exact rowAxis_mirror R h l v
  | oldAxis i g k =>
      apply padPartition_mirror
      intro b
      unfold oldAxisPartition
      apply joint_mirror
      · intro c
        exact binary_mirror (amplify (RowSlots.dimension R) (E i)) (amplify (RowSlots.dimension R) (F i))
          (amplify_projection _ _ (hE i)) (amplify_projection _ _ (hF i))
          (entangle (RowSlots.dimension R) v) (amplify_mirror (RowSlots.dimension R) (E i) (F i) v (hm i)) c
      · intro c
        apply reflection_mirror
        exact rowAxis_mirror R g k v
  | global isX =>
      cases isX
      · apply padPartition_mirror
        intro b
        simp only [RowScalar.dimension_bits]
        exact diagonal_mirror _ b v
      · apply padPartition_mirror
        intro b
        simp only [RowScalar.dimension_bits]
        exact fourier_mirror _ b v
  | pair j =>
      dsimp only [newPartition]
      split_ifs with hj
      · apply padPartition_mirror
        intro b
        simp only [RowScalar.dimension_bits]
        exact pair_mirror _ j hj v b
      · exact deterministic_mirror _ _ _
  | slot r j =>
      dsimp only [newPartition]
      split_ifs with hj
      · apply padPartition_mirror
        intro b
        simp only [RowScalar.dimension_bits]
        apply slotPartition_mirror
        cases he : (RowSlots.slot R r j).event with
        | none => simp only [slotEvent,he,left_one,right_one]
        | some i => simpa only [slotEvent,he] using hm i
      · exact deterministic_mirror _ _ _
  | column r =>
      apply padPartition_mirror
      intro b
      exact columnEffect_mirror R E F hE hF v hm r b

end Sigma2.RowCompleteness
