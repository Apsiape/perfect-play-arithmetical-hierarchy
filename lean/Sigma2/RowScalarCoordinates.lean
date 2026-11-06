import Sigma2.RowScalarRestriction
import Sigma2.MatrixSupportDensity

/-! Numbered soundness step 1: the actual two-sided scalar
support coordinates, trace-one corner densities and old named projections.
PiLp 2 is the completed finite Hilbert direct sum, equivalently C^d tensor
its corner. No coordinate decomposition is assumed by any caller. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame Preliminaries MatrixSupportCoordinates

/-- Every support/corner coordinate space is a closed Hilbert subspace. -/
instance coordinateSpaceComplete (P : Op) : CompleteSpace (space P) := by
  unfold space
  exact (P-1).isClosed_ker.completeSpace_coe

#print axioms coordinateSpaceComplete

def zeroRegister : (n : ℕ) → Register n
  | 0 => ()
  | n+1 => ((0,0),zeroRegister n)

private theorem corner_projection {ι : Type} [Fintype ι] [DecidableEq ι]
    {P : Op} {t : ι → ι → Op} (hu : Units P t) (A : Op) (hA : Projection A)
    (hc : ∀ i j,Commute A (t i j)) (o : ι) :
    Projection (A*t o o) ∧ (A*t o o)*t o o=A*t o o ∧
      t o o*(A*t o o)=A*t o o ∧
      ∀ i v,t o i (A v)=(A*t o o) (t o i v) := by
  have ht := hu.diagonal_projection o
  refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
  · rw [star_mul,hA.1,ht.1]
    exact (hc o o).eq.symm
  · calc
      _ = A*(t o o*A)*t o o := by noncomm_ring
      _ = A*(A*t o o)*t o o := by rw [(hc o o).eq]
      _ = (A*A)*(t o o*t o o) := by noncomm_ring
      _ = A*t o o := by rw [hA.2,ht.2]
  · rw [mul_assoc,ht.2]
  · rw [← mul_assoc,← (hc o o).eq,mul_assoc,ht.2]
  · intro i v
    change (t o i*A) v=((A*t o o)*t o i) v
    rw [mul_assoc,hu.product,if_pos rfl]
    exact congrArg (fun B : Op => B v) (hc o i).eq.symm

/-- Actual Alice support realization, including every named projection of
the exact restricted strategy and the normalized trace-class corner density. -/
theorem scalar_support_alice (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P) :
    let t := tensorUnit P (localUnit G R S.measurements P)
    let o := zeroRegister (RowSlots.squares R)
    ∃ h0 : Density, ∃ U : space P ≃ₗᵢ[ℂ]
        PiLp 2 (fun _ : Register (RowSlots.squares R) => space (t o o)),
      SupportOf h0 (t o o) ∧ h0.op=(RowSlots.dimension R:ℂ) • (h.op*t o o) ∧
      (∀ v i,((U v) i:H)=t o i v) ∧
      (∀ w,(U.symm w:H)=∑ i,t i o (w i)) ∧
      (∀ i j k v,t o k (t i j v)=if k=i then t o j v else 0) ∧
      (∀ i v,t o i (h.op v)=(RowSlots.dimension R:ℂ)⁻¹ • h0.op (t o i v)) ∧
      ∀ a : Fin R.count,∃ e : Op,Projection e ∧ e*t o o=e ∧ t o o*e=e ∧
        ∀ i v,t o i ((P*(RowRestriction.restrict G R S).measurements.alice
          (R.event a).x (R.event a).a*P) v)=e (t o i v) := by
  let t := tensorUnit P (localUnit G R S.measurements P)
  let o := zeroRegister (RowSlots.squares R)
  have ht := common_matrix_units G R S hS h hm P hP
  let hu : Units P t := ⟨ht.1,ht.2.1,ht.2.2⟩
  have hc := common_units_centralize G R S hS h hm P hP
  have hd : Fintype.card (Register (RowSlots.squares R))=RowSlots.dimension R := register_card _
  refine ⟨hu.cornerDensity h hP hc o,hu.coordinates o,
    hu.cornerDensity_support h hP hc o,?_,?_,?_,?_,?_,?_⟩
  · change (Fintype.card (Register (RowSlots.squares R)):ℂ) • (h.op*t o o)=_
    rw [hd]
  · exact fun v i => hu.coordinates_apply o i v
  · exact fun w => hu.coordinates_symm_apply o w
  · exact fun i j k v => hu.unit_coordinates o i j k v
  · simpa only [hd] using hu.density_coordinates h hP hc o
  · intro a
    have he := corner_projection hu (oldEffect G R S.measurements P a)
      (old_projection G R S hS h hm P hP a)
      (old_units_commute G R S hS h hm P hP a) o
    refine ⟨oldEffect G R S.measurements P a*t o o,he.1,he.2.1,he.2.2.1,?_⟩
    intro i v
    rw [restriction_alice_effect G R S hS h hm P hP]
    exact he.2.2.2 i v

/-- The same realization on Bob's own original support, using the common
transposed reversed-word scalar algebra and his supplied original marginal. -/
theorem scalar_support_bob (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalB S h) (Q : Op) (hQ : SupportOf h Q) :
    let t := bobTensor G R S.measurements Q
    let o := zeroRegister (RowSlots.squares R)
    ∃ h0 : Density, ∃ U : space Q ≃ₗᵢ[ℂ]
        PiLp 2 (fun _ : Register (RowSlots.squares R) => space (t o o)),
      SupportOf h0 (t o o) ∧ h0.op=(RowSlots.dimension R:ℂ) • (h.op*t o o) ∧
      (∀ v i,((U v) i:H)=t o i v) ∧
      (∀ w,(U.symm w:H)=∑ i,t i o (w i)) ∧
      (∀ i j k v,t o k (t i j v)=if k=i then t o j v else 0) ∧
      (∀ i v,t o i (h.op v)=(RowSlots.dimension R:ℂ)⁻¹ • h0.op (t o i v)) ∧
      ∀ a : Fin R.count,∃ e : Op,Projection e ∧ e*t o o=e ∧ t o o*e=e ∧
        ∀ i v,t o i ((Q*(RowRestriction.restrict G R S).measurements.bob
          (R.event a).y (R.event a).b*Q) v)=e (t o i v) := by
  let t := bobTensor G R S.measurements Q
  let o := zeroRegister (RowSlots.squares R)
  have ht := bob_matrix_units G R S hS h hm Q hQ
  let hu : Units Q t := ⟨ht.1,ht.2.1,ht.2.2⟩
  have hc := bob_units_centralize G R S hS h hm Q hQ
  have hd : Fintype.card (Register (RowSlots.squares R))=RowSlots.dimension R := register_card _
  refine ⟨hu.cornerDensity h hQ hc o,hu.coordinates o,
    hu.cornerDensity_support h hQ hc o,?_,?_,?_,?_,?_,?_⟩
  · change (Fintype.card (Register (RowSlots.squares R)):ℂ) • (h.op*t o o)=_
    rw [hd]
  · exact fun v i => hu.coordinates_apply o i v
  · exact fun w => hu.coordinates_symm_apply o w
  · exact fun i j k v => hu.unit_coordinates o i j k v
  · simpa only [hd] using hu.density_coordinates h hQ hc o
  · intro a
    have he := corner_projection hu (oldBobEffect G R S.measurements Q a)
      (old_bob_projection G R S hS h hm Q hQ a)
      (old_bob_units_commute G R S hS h hm Q hQ a) o
    refine ⟨oldBobEffect G R S.measurements Q a*t o o,he.1,he.2.1,he.2.2.1,?_⟩
    intro i v
    rw [restriction_bob_effect G R S hS h hm Q hQ]
    exact he.2.2.2 i v

#print axioms scalar_support_alice
#print axioms scalar_support_bob

/-- Numbered soundness step 1, from perfection alone: both original normal
supports, explicit common scalar coordinates, faithful trace-one corner densities,
and the exact restricted old named projections in their scalar commutants. -/
theorem scalar_support_two_sided (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S) :
    ∃ (hA hB : Density) (P Q : Op),
      MarginalA S hA ∧ MarginalB S hB ∧ SupportOf hA P ∧ SupportOf hB Q ∧
      let tA := tensorUnit P (localUnit G R S.measurements P)
      let tB := bobTensor G R S.measurements Q
      let o := zeroRegister (RowSlots.squares R)
      ∃ (hA0 hB0 : Density)
        (UA : space P ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Register (RowSlots.squares R) => space (tA o o)))
        (UB : space Q ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Register (RowSlots.squares R) => space (tB o o))),
        SupportOf hA0 (tA o o) ∧ SupportOf hB0 (tB o o) ∧
        hA0.op=(RowSlots.dimension R:ℂ) • (hA.op*tA o o) ∧
        hB0.op=(RowSlots.dimension R:ℂ) • (hB.op*tB o o) ∧
        (∀ v i,((UA v) i:H)=tA o i v) ∧ (∀ v i,((UB v) i:H)=tB o i v) ∧
        (∀ w,(UA.symm w:H)=∑ i,tA i o (w i)) ∧
        (∀ w,(UB.symm w:H)=∑ i,tB i o (w i)) ∧
        (∀ i v,tA o i (hA.op v)=(RowSlots.dimension R:ℂ)⁻¹ • hA0.op (tA o i v)) ∧
        (∀ i v,tB o i (hB.op v)=(RowSlots.dimension R:ℂ)⁻¹ • hB0.op (tB o i v)) ∧
        (∀ a : Fin R.count,∃ e : Op,Projection e ∧ e*tA o o=e ∧ tA o o*e=e ∧
          ∀ i v,tA o i ((P*(RowRestriction.restrict G R S).measurements.alice
            (R.event a).x (R.event a).a*P) v)=e (tA o i v)) ∧
        (∀ a : Fin R.count,∃ e : Op,Projection e ∧ e*tB o o=e ∧ tB o o*e=e ∧
          ∀ i v,tB o i ((Q*(RowRestriction.restrict G R S).measurements.bob
            (R.event a).y (R.event a).b*Q) v)=e (tB o i v)) := by
  obtain ⟨hA,hB,hmA,hmB⟩ := marginals_exist S
  obtain ⟨P,hP⟩ := support_exists hA
  obtain ⟨Q,hQ⟩ := support_exists hB
  obtain ⟨hA0,UA,haS,haN,haF,haB,haU,haD,haE⟩ := scalar_support_alice G R S hS hA hmA P hP
  obtain ⟨hB0,UB,hbS,hbN,hbF,hbB,hbU,hbD,hbE⟩ := scalar_support_bob G R S hS hB hmB Q hQ
  exact ⟨hA,hB,P,Q,hmA,hmB,hP,hQ,hA0,hB0,UA,UB,
    haS,hbS,haN,hbN,haF,hbF,haB,hbB,haD,hbD,haE,hbE⟩

#print axioms scalar_support_two_sided
#print axioms corner_projection

end Sigma2.RowScalar