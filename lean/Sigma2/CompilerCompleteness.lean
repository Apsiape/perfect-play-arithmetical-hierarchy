import Sigma2.CompilerApproxBase
import Sigma2.CompilerCompleteSupport
import Sigma2.CompilerEntropyInterface
import Sigma2.CompilerContract
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerCompleteness
open Compiler CompilerScaffold CompilerEventLoss CompilerApproxRows
  CompilerApproxDictionaryEnergy CompilerApproxEnergy CompilerApproxIndex CompilerApproxStrategy
  CompilerApproxBase CompilerCompleteSupport CompilerEventSlots RowCompleteness TensorLifts
attribute [local irreducible] names rowList words polynomials structuralPolynomials applicationPolynomials rowsBefore

/-- Equality of occupied named actions transfers the literal finite row sum. -/
theorem named_row_action {s} (Q : Rows s) (S : NormalStrategy s)
    (E : Fin Q.count → Op)
    (hE : ∀ i k,0<S.weight k → left (E i) (S.vector k)=
      S.measurements.left (Q.event i).x (Q.event i).a (S.vector k))
    (r : Fin Q.rowCount) (k : ℕ) (hk : 0<S.weight k) :
    left (rowOperator Q E r) (S.vector k)=
      left (rowOperator Q (fun i => S.measurements.alice (Q.event i).x (Q.event i).a) r)
        (S.vector k) := by
  simp only [rowOperator,DiagonalIdentification.left_add,MagicRelations.left_smul,left_sum,
    left_one,add_apply,smul_apply,sum_apply,one_apply_eq_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hE i k hk,measurements_left]

/-- Synchronization transfers each row sum from Alice to Bob on occupied vectors. -/
theorem mirrored_row_action {s} (Q : Rows s) (S : NormalStrategy s)
    (hmir : ∀ i k,0<S.weight k →
      S.measurements.left (Q.event i).x (Q.event i).a (S.vector k)=
      S.measurements.right (Q.event i).y (Q.event i).b (S.vector k))
    (r : Fin Q.rowCount) (k : ℕ) (hk : 0<S.weight k) :
    left (rowOperator Q (fun i => S.measurements.alice (Q.event i).x (Q.event i).a) r)
      (S.vector k)=
    right (rowOperator Q (fun i => S.measurements.bob (Q.event i).y (Q.event i).b) r)
      (S.vector k) := by
  simp only [rowOperator,DiagonalIdentification.left_add,DiagonalIdentification.right_add,
    MagicRelations.left_smul,MagicRelations.right_smul,left_sum,right_sum,
    left_one,right_one,add_apply,smul_apply,sum_apply,one_apply_eq_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hh := hmir i k hk
  rw [measurements_left,measurements_right] at hh
  rw [hh]

/-- Exact residual matching supplies the application density annihilators. -/
theorem application_row_density_zero (P : Presentation) (hP : P.admissible)
    (R : StructuralRealization P)
    (hz : ∀ A,A∈applicationResiduals P R → A=0)
    (j : Fin (applicationPolynomials P).length) :
    rowOperator (rows P) (numbered R) (rowIndex P j)*(oldDensity R).op=0 := by
  have hr : residualAt P R j=0 := by
    rw [residualAt_get]
    apply hz
    exact List.getElem_mem _
  have he := CompilerApproxEnergy.residual_matching P hP R j
  dsimp only at he
  simp only [hr,mul_zero] at he
  have ht : (trace (0:Op)).re=0 := by simp [trace,entry]
  rw [ht,mul_zero] at he
  apply mul_density_zero_of_energy (oldDensity R)
  rw [rowOperator_selfadjoint (rows P) (numbered R) (numbered_projection R)]
  exact he

/-- Structural rows plus vanishing application residuals give the frozen full
RowsHold record, on the original mixed strategy and its original marginals. -/
theorem rowsHold_of_zero_residuals (P : Presentation) (hP : P.admissible)
    (R : StructuralRealization P) (S : NormalStrategy (preGame P).scenario)
    (hR : StructuralRowsHold P S) (hmarg : MarginalA S (oldDensity R))
    (hn : NamedProjections15 P R S)
    (hz : ∀ A,A∈applicationResiduals P R → A=0) : RowsHold (rows P) S := by
  obtain ⟨hA,hB,hmA,hmB,hmir,ha,hb⟩ := hR
  have happ (r : Fin (rows P).rowCount) (hr : applicationRow P r)
      (k : ℕ) (hk : 0<S.weight k) :
      left (rowOperator (rows P)
        (fun i => S.measurements.alice ((rows P).event i).x ((rows P).event i).a) r)
        (S.vector k)=0 := by
    obtain ⟨j,rfl⟩ := application_index P r hr
    rw [← named_row_action (rows P) S (numbered R) hn (rowIndex P j) k hk]
    exact normal_left_zero S (oldDensity R) hmarg _
      (application_row_density_zero P hP R hz j) k hk
  refine ⟨hA,hB,hmA,hmB,hmir,?_,?_⟩
  · intro r
    by_cases hr : applicationRow P r
    · exact mul_marginalA_zero S hA hmA _ (happ r hr)
    · exact ha r hr
  · intro r
    by_cases hr : applicationRow P r
    · apply mul_marginalB_zero S hB hmB
      intro k hk
      exact (mirrored_row_action (rows P) S hmir r k hk).symm.trans (happ r hr k hk)
    · exact hb r hr

theorem rowsHold_normal (P : Presentation) (hP : P.admissible)
    (R : NormalRealization P) (S : NormalStrategy (preGame P).scenario)
    (hR : StructuralRowsHold P S)
    (hmarg : MarginalA S (oldDensity (CompilerHonestRealization.structural R)))
    (hn : NamedProjections15 P (CompilerHonestRealization.structural R) S) :
    RowsHold (rows P) S :=
  rowsHold_of_zero_residuals P hP _ S hR hmarg hn
    (CompilerHonestRealization.application_residual_zero R)

/-- Apply the literal frozen RowCompleteness theorem, including its extension
and entropy-preservation clauses, to the corrected base interface. -/
theorem extension_of_base15 (P : Presentation) (hP : P.admissible)
    (H : BaseObligation15 P) (R : NormalRealization P) :
    ∃ S : NormalStrategy (preGame P).scenario,
      ∃ T : NormalStrategy (finalGame P).scenario,
        Perfect (preGame P) S ∧ RowsHold (rows P) S ∧ NamedBinaryProjections (rows P) S ∧
        Perfect (finalGame P) T ∧ Extends (RowGame.embedding (preGame P) (rows P)) S T ∧
        (RealizationFiniteEntropy R → FiniteMarginalEntropy S) ∧
        (FiniteMarginalEntropy S → FiniteMarginalEntropy T) := by
  obtain ⟨S,hS,hN,hR,hm,hn,hB⟩ := H (CompilerHonestRealization.structural R)
  have hfull := rowsHold_normal P hP R S hR hm hn
  obtain ⟨T,hT,hext,hent⟩ := RowCompleteness.completeness (preGame P) (rows P) S hS hfull hN
  refine ⟨S,T,hS,hfull,hN,hT,hext,?_,hent⟩
  intro hE
  exact CompilerEntropyInterface.finiteMarginalEntropy_of_bob
    (CompilerHonestRealization.structural R) S hm hE (hB hE)

theorem completeness_of_base15 (P : Presentation) (hP : P.admissible)
    (H : BaseObligation15 P) : CompilerContract.Completeness P := by
  rintro ⟨R⟩
  obtain ⟨S,T,_,_,_,hT,_,_,_⟩ := extension_of_base15 P hP H R
  exact ⟨T,hT⟩

theorem finiteEntropyCompleteness_of_base15 (P : Presentation) (hP : P.admissible)
    (H : BaseObligation15 P) : CompilerContract.FiniteEntropyCompleteness P := by
  rintro ⟨R,hE⟩
  obtain ⟨S,T,_,_,_,hT,_,hS,hent⟩ := extension_of_base15 P hP H R
  exact ⟨T,hT,hent (hS hE)⟩

/-- The four independent soundness inputs and the single corrected base input
supply all seven unchanged assembly obligations. -/
theorem obligations_of_base15 (P : Presentation) (hP : P.admissible)
    (H : BaseObligation15 P)
    (hs : CompilerContract.Soundness P)
    (he : CompilerContract.FiniteEntropySoundness P)
    (hf : CompilerContract.FiniteSupportSoundness P)
    (hsrc : CompilerContract.SourceEventSoundness P) : CompilerContract.Obligations P :=
  ⟨hs,he,hf,hsrc,completeness_of_base15 P hP H,
    finiteEntropyCompleteness_of_base15 P hP H,approxCompiled_of_base15 P hP H⟩

/-- No base witness is asserted: this is the exact one remaining clock development Prop. -/
def RemainingClockProp15 : Prop := ∀ P : Presentation,P.admissible → BaseObligation15 P

theorem lemma_4_4_strong_of_base15
    (H : RemainingClockProp15)
    (hs : ∀ P : Presentation,P.admissible → CompilerContract.Soundness P)
    (he : ∀ P : Presentation,P.admissible → CompilerContract.FiniteEntropySoundness P)
    (hf : ∀ P : Presentation,P.admissible → CompilerContract.FiniteSupportSoundness P)
    (hsrc : ∀ P : Presentation,P.admissible → CompilerContract.SourceEventSoundness P) :
    ∃ f : ℕ → ℕ,Computable f ∧ ∀ code P,
      Encodable.decode (α := Presentation) code=some P → P.admissible →
        Compiled P (f code) ∧ ApproxCompiled P (f code) := by
  apply CompilerContract.lemma_4_4_strong_of_obligations
  intro P hp
  exact obligations_of_base15 P hp (H P hp) (hs P hp) (he P hp) (hf P hp) (hsrc P hp)

#print axioms named_row_action
#print axioms mirrored_row_action
#print axioms application_row_density_zero
#print axioms rowsHold_of_zero_residuals
#print axioms rowsHold_normal
#print axioms extension_of_base15
#print axioms completeness_of_base15
#print axioms finiteEntropyCompleteness_of_base15
#print axioms obligations_of_base15
#print axioms RemainingClockProp15
#print axioms lemma_4_4_strong_of_base15
#print BaseObligation15
#print RemainingClockProp15
end Sigma2.CompilerCompleteness
