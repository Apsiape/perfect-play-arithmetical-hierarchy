import Sigma2.RowScalarGlobal
import Sigma2.MirrorUnits

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame TensorLifts Preliminaries CoarseCells FiniteSpectral MirrorUnits

def bobBinary (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P : Op) (q : NewQ R) : Op :=
  signed (compressed P (M.bob (qb G R q))) (fun a => binaryClass a.val)

private theorem signed_star {ι : Type} [Fintype ι] (P : Op) (hP : Projection P)
    (A : ι → Op) (hA : ∀ i,Positive (A i)) (f : ι → Fin 4) :
    star (signed (compressed P A) f)=signed (compressed P A) f := by
  exact (star_sub _ _).trans (congrArg₂ (fun X Y : Op => X-Y)
    (coarse_positive _ f 1 (compressed_positive P hP A hA)).isSelfAdjoint.star_eq
    (coarse_positive _ f 2 (compressed_positive P hP A hA)).isSelfAdjoint.star_eq)

theorem binary_mirror (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (hA hB : Density) (hmA : MarginalA (normalOfPure S) hA)
    (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) (q : NewQ R) :
    AdjointMirror S.vector (binary G R S.measurements P q) (bobBinary G R S.measurements Q q) := by
  apply adjointMirror_self
  · exact signed_star P hP.1 _ (S.measurements.alice_pos _) _
  · exact signed_star Q hQ.1 _ (S.measurements.bob_pos _) _
  · have he (t : Fin 4) := MirrorAlgebra.compressed_mirror S.vector P Q _ _
      (MirrorAlgebra.left_support S hA hmA P hP)
      (MirrorAlgebra.right_support S hB hmB Q hQ)
      (bound_analysis G R S hS hA hmA P hP q q binaryClass binaryClass
        (diagonal_reject R q.val binaryClass) t).1
    simpa only [binary,bobBinary,signed,coarse_compressed,PureSupport.left_sub,MagicRelations.right_sub,
      sub_apply] using congrArg₂ (fun v w : AB => v-w) (he 1) (he 2)

def bobLocal (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (Q : Op) (g : Fin (RowSlots.squares R)) (i j : FourUnits.Index) : Op :=
  oppositeQubit Q (bobBinary G R M Q (axisQ R g 3)) (bobBinary G R M Q (axisQ R g 1)) j.2 i.2 *
  oppositeQubit Q (bobBinary G R M Q (axisQ R g 2)) (bobBinary G R M Q (axisQ R g 0)) j.1 i.1

def reverseTensor (P : Op) : {n : ℕ} → (Fin n → FourUnits.Index → FourUnits.Index → Op) →
    Register n → Register n → Op
  | 0,_,_,_ => P
  | n+1,U,i,j => reverseTensor P (fun g => U g.succ) i.2 j.2*U 0 i.1 j.1

def bobTensor (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (Q : Op) : Register (RowSlots.squares R) → Register (RowSlots.squares R) → Op :=
  reverseTensor Q (bobLocal G R M Q)

private theorem tensor_mirror (v : AB) (P Q : Op) {n : ℕ}
    (U V : Fin n → FourUnits.Index → FourUnits.Index → Op)
    (he : AdjointMirror v P Q) (hm : ∀ g i j,AdjointMirror v (U g i j) (V g j i))
    (i j : Register n) :
    AdjointMirror v (tensorUnit P U i j) (reverseTensor Q V j i) := by
  induction n with
  | zero => exact he
  | succ n ih =>
    exact adjointMirror_mul _ _ _ _ _ (hm 0 i.1 j.1)
      (ih _ _ (fun g => hm g.succ) i.2 j.2)

/-- A common Alice unit mirrors the transposed Bob unit, with every word
reversed in the actual Bob-only operators. -/
theorem common_units_mirror (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (hA hB : Density) (hmA : MarginalA (normalOfPure S) hA)
    (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q)
    (i j : Register (RowSlots.squares R)) :
    AdjointMirror S.vector (tensorUnit P (localUnit G R S.measurements P) i j)
      (bobTensor G R S.measurements Q j i) := by
  have he : AdjointMirror S.vector P Q := adjointMirror_self _ _ _ hP.1.1 hQ.1.1
    ((MirrorAlgebra.left_support S hA hmA P hP).trans (MirrorAlgebra.right_support S hB hmB Q hQ).symm)
  apply tensor_mirror S.vector P Q _ _ he
  intro g a b
  exact adjointMirror_mul _ _ _ _ _
    (adjointMirror_qubit _ _ _ _ _ _ _ he
      (binary_mirror G R S hS hA hB hmA hmB P Q hP hQ (axisQ R g 2))
      (binary_mirror G R S hS hA hB hmA hmB P Q hP hQ (axisQ R g 0)) a.1 b.1)
    (adjointMirror_qubit _ _ _ _ _ _ _ he
      (binary_mirror G R S hS hA hB hmA hmB P Q hP hQ (axisQ R g 3))
      (binary_mirror G R S hS hA hB hmA hmB P Q hP hQ (axisQ R g 1)) a.2 b.2)

private theorem opposite_bisupported (P X Z : Op) (hP : Projection P)
    (hX : P*X=X ∧ X*P=X) (hZ : P*Z=Z ∧ Z*P=Z) (i j : Fin 2) :
    P*oppositeQubit P X Z i j=oppositeQubit P X Z i j ∧
      oppositeQubit P X Z i j*P=oppositeQubit P X Z i j := by
  have hp : P*PauliMatrixUnits.projector P Z j=PauliMatrixUnits.projector P Z j := by
    simp only [PauliMatrixUnits.projector,mul_smul_comm,mul_add,hP.2,hZ.1]
  constructor
  · unfold oppositeQubit
    split_ifs
    · exact hp
    · rw [← mul_assoc,hp]
  · exact opposite_supported P P X Z hP.2 hX.2 hZ.2 i j

theorem bobTensor_supported (G : Game) (R : Rows G.scenario)
    (M : Measurements (scenario G R)) (Q : Op) (hQ : Projection Q)
    (i j : Register (RowSlots.squares R)) :
    Q*bobTensor G R M Q i j=bobTensor G R M Q i j ∧
      bobTensor G R M Q i j*Q=bobTensor G R M Q i j := by
  have hb (q : NewQ R) : Q*bobBinary G R M Q q=bobBinary G R M Q q ∧
      bobBinary G R M Q q*Q=bobBinary G R M Q q := by
    unfold bobBinary signed
    rw [coarse_compressed,coarse_compressed]
    constructor
    · simp only [mul_sub,← mul_assoc,hQ.2]
    · simp only [sub_mul,mul_assoc,hQ.2]
  have hl (g : Fin (RowSlots.squares R)) (a b : FourUnits.Index) :
      Q*bobLocal G R M Q g a b=bobLocal G R M Q g a b ∧
      bobLocal G R M Q g a b*Q=bobLocal G R M Q g a b := by
    have h1 := opposite_bisupported Q _ _ hQ (hb (axisQ R g 3)) (hb (axisQ R g 1)) b.2 a.2
    have h2 := opposite_bisupported Q _ _ hQ (hb (axisQ R g 2)) (hb (axisQ R g 0)) b.1 a.1
    exact ⟨by change Q*(_*_)=_; rw [← mul_assoc,h1.1]; rfl,
      by change (_*_)*Q=_; rw [mul_assoc,h2.2]; rfl⟩
  suffices ∀ {n} (U : Fin n → FourUnits.Index → FourUnits.Index → Op),
      (∀ g a b,Q*U g a b=U g a b ∧ U g a b*Q=U g a b) →
      ∀ i j : Register n,Q*reverseTensor Q U i j=reverseTensor Q U i j ∧
        reverseTensor Q U i j*Q=reverseTensor Q U i j from this _ hl i j
  intro n U hs i j
  induction n with
  | zero => exact ⟨hQ.2,hQ.2⟩
  | succ n ih =>
    have ht := ih (fun g => U g.succ) (fun g => hs g.succ) i.2 j.2
    exact ⟨by change Q*(_*_)=_; rw [← mul_assoc,ht.1]; rfl,
      by change (_*_)*Q=_; rw [mul_assoc,(hs 0 i.1 j.1).2]; rfl⟩

/-- Full multiplication, adjoints and completeness on Bob's original support. -/
theorem pure_bob_matrix_units (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (hA hB : Density) (hmA : MarginalA (normalOfPure S) hA)
    (hmB : MarginalB (normalOfPure S) hB)
    (P Q : Op) (hP : SupportOf hA P) (hQ : SupportOf hB Q) :
    let u := bobTensor G R S.measurements Q
    (∀ i j k l,u i j*u k l=if j=k then u i l else 0) ∧
      (∀ i j,star (u i j)=u j i) ∧ (∑ i,u i i)=Q := by
  let t := tensorUnit P (localUnit G R S.measurements P)
  let u := bobTensor G R S.measurements Q
  have ht := common_matrix_units G R (normalOfPure S) hS hA hmA P hP
  change (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
    (∀ i j,star (t i j)=t j i) ∧ (∑ i,t i i)=P at ht
  have hm := common_units_mirror G R S hS hA hB hmA hmB P Q hP hQ
  have hs := bobTensor_supported G R S.measurements Q hQ.1
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro i j k l
    apply right_local_eq S hB hmB Q hQ _ _ (by rw [mul_assoc,(hs k l).2])
      (by split_ifs <;> simp only [(hs i l).2,zero_mul])
    have hh := MirrorAlgebra.mirror_mul S.vector _ _ _ _ (hm l k).1 (hm j i).1
    change left (t l k*t j i) S.vector=right (u i j*u k l) S.vector at hh
    rw [ht.1 l k j i] at hh
    by_cases hjk : j=k
    · simp only [hjk,ite_true] at hh ⊢
      exact hh.symm.trans (hm l i).1
    · simpa only [hjk,Ne.symm hjk,ite_false,left_zero,right_zero,map_zero] using hh.symm
  · intro i j
    refine right_local_eq S hB hmB Q hQ _ _ ?_ (hs j i).2 ?_
    · have hh := congrArg star (hs i j).1
      simpa only [star_mul,hQ.1.1] using hh
    · rw [← (hm j i).2]
      change left (star (t j i)) S.vector=_
      rw [ht.2.1 j i]
      exact (hm i j).1
  · apply right_local_eq S hB hmB Q hQ _ _
      (by simp only [Finset.sum_mul,(hs _ _).2]) hQ.1.2
    rw [right_sum,sum_apply]
    change (∑ i,right (u i i) S.vector)=right Q S.vector
    calc
      _ = ∑ i,left (t i i) S.vector := by
        apply Finset.sum_congr rfl
        intro i _
        exact (hm i i).1.symm
      _ = left (∑ i,t i i) S.vector := by rw [left_sum,sum_apply]
      _ = right Q S.vector := by
        rw [ht.2.2,MirrorAlgebra.left_support S hA hmA P hP,
          MirrorAlgebra.right_support S hB hmB Q hQ]

/-- Bob's actual normal operators and supplied marginal survive purification. -/
theorem bob_matrix_units (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q) :
    let u := bobTensor G R S.measurements Q
    (∀ i j k l,u i j*u k l=if j=k then u i l else 0) ∧
      (∀ i j,star (u i j)=u j i) ∧ (∑ i,u i i)=Q := by
  obtain ⟨T,hB,hM,hprob⟩ := Purification.exists_pure_preserving_bob S
  obtain ⟨hA,_,hmA,_⟩ := marginals_exist (normalOfPure T)
  obtain ⟨P,hP⟩ := support_exists hA
  have hh := pure_bob_matrix_units G R T (pure_perfect_transfer G R S hS T hprob)
    hA h hmA (hM h hm) P Q hP hQ
  have hl : bobLocal G R T.measurements Q=bobLocal G R S.measurements Q := by
    funext g i j
    simp only [bobLocal,bobBinary,hB,Purification.measurements,TensorLifts.measurements]
  simpa only [bobTensor,hl] using hh

#print axioms binary_mirror
#print axioms common_units_mirror
#print axioms bob_matrix_units

/-- Bob's original marginal centralizes every reversed-word scalar unit. -/
theorem bob_units_centralize (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q)
    (i j : Register (RowSlots.squares R)) :
    Commute h.op (bobTensor G R S.measurements Q i j) := by
  have hp := MatrixCentralizer.support_centralizes h Q hQ
  have hb (q : NewQ R) : Commute h.op (bobBinary G R S.measurements Q q) := by
    have hf (a : BB (scenario G R)) : Commute h.op
        (compressed Q (S.measurements.bob (qb G R q)) a) :=
      (hp.mul_right (new_sharp_bob G R S hS h hm Q hQ q a).2).mul_right hp
    have hc (t : Fin 4) : Commute h.op
        (coarse (compressed Q (S.measurements.bob (qb G R q))) (fun a => binaryClass a.val) t) := by
      apply Commute.sum_right
      intro a _
      split_ifs
      · exact hf a
      · exact Commute.zero_right _
    exact (hc 1).sub_right (hc 2)
  have ho (X Z : Op) (hx : Commute h.op X) (hz : Commute h.op Z) (a b : Fin 2) :
      Commute h.op (oppositeQubit Q X Z a b) := by
    have hz' := FourUnits.commute_projector h.op Q Z hp hz b
    unfold oppositeQubit
    split_ifs
    · exact hz'
    · exact hz'.mul_right hx
  have hl (g a b) : Commute h.op (bobLocal G R S.measurements Q g a b) :=
    (ho _ _ (hb (axisQ R g 3)) (hb (axisQ R g 1)) b.2 a.2).mul_right
      (ho _ _ (hb (axisQ R g 2)) (hb (axisQ R g 0)) b.1 a.1)
  suffices ∀ {n} (U : Fin n → FourUnits.Index → FourUnits.Index → Op),
      (∀ g a b,Commute h.op (U g a b)) →
      ∀ i j : Register n,Commute h.op (reverseTensor Q U i j) from this _ hl i j
  intro n U hs i j
  induction n with
  | zero => exact hp
  | succ n ih => exact (ih _ (fun g => hs g.succ) i.2 j.2).mul_right (hs 0 i.1 j.1)

#print axioms bob_units_centralize
#print axioms signed_star
#print axioms tensor_mirror
#print axioms opposite_bisupported
#print axioms bobTensor_supported
#print axioms pure_bob_matrix_units

end Sigma2.RowScalar