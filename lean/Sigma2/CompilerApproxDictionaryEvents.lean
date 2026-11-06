import Sigma2.CompilerApproxDictionaryBound

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxDictionaryEvents
open Compiler CompilerScaffold CompilerEventCounting CompilerEventLoss CompilerEventClasses
  CompilerApproxDictionaryIndex CompilerApproxDictionaryEnergy CompilerApproxDictionaryBound CompilerApproxDecoder
attribute [local irreducible] names rowList words polynomials structuralPolynomials applicationPolynomials

 theorem application_shape (P : Presentation) (x y a b)
    (hc : testClass P x y a b=.applicationForward ∨ testClass P x y a b=.applicationReverse) :
    ∃ r : Fin (rows P).rowCount,applicationRow P r ∧ a=0 ∧ b=0 ∧
      ((RowGame.decodeA (preGame P) (rows P) x=.inr (.column r) ∧
        RowGame.decodeB (preGame P) (rows P) y=.inr (.global true)) ∨
       (RowGame.decodeA (preGame P) (rows P) x=.inr (.global true) ∧
        RowGame.decodeB (preGame P) (rows P) y=.inr (.column r))) := by
  unfold testClass at hc
  split at hc <;> (try (split at hc)) <;> aesop

 theorem rowContribution_eq (P : Presentation) (S : NormalStrategy (finalGame P).scenario)
    (r : Fin (rows P).rowCount) :
    rowContribution P S r=
      (1/(questionCount P:ℝ)^2)*rejection P S
        (RowScalar.qa (preGame P) (rows P) (columnQuestion (rows P) r))
        (RowScalar.qb (preGame P) (rows P) (referenceQuestion (rows P))) 0 0+
      (1/(questionCount P:ℝ)^2)*rejection P S
        (RowScalar.qa (preGame P) (rows P) (referenceQuestion (rows P)))
        (RowScalar.qb (preGame P) (rows P) (columnQuestion (rows P) r)) 0 0 := by
  unfold rowContribution bothZeroContribution rejection
  rw [final_distribution,final_distribution]

 theorem application_event_bound (P : Presentation) (hP : P.admissible) (R : StructuralRealization P)
    (S : NormalStrategy (finalGame P).scenario) (hS : HonestApplicationRows P R S)
    (x y a b) (hc : testClass P x y a b=.applicationForward ∨ testClass P x y a b=.applicationReverse) :
    (1/(questionCount P:ℝ)^2)*rejection P S x y a b≤(16*∑ i,baseWeight P i)*energyTotal P R := by
  obtain ⟨r,hr,ha,hb,hf|hv⟩ := application_shape P x y a b hc
  · obtain ⟨hx,hy⟩ := hf
    have hxc := qa_of_decode (preGame P) (rows P) (columnQuestion (rows P) r)
      (le_of_eq (CompilerApproxDecoder.column_count (rows P) r)) (by simp [columnQuestion]) x hx
    have hyr := qb_of_decode (preGame P) (rows P) (referenceQuestion (rows P))
      (le_of_eq (CompilerApproxDecoder.reference_count (rows P))) (by simp [referenceQuestion]) y hy
    subst x; subst y; subst a; subst b
    obtain ⟨j,rfl⟩ := application_index P r hr
    apply le_trans _ (row_bound P hP R S hS j)
    rw [rowContribution_eq]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (rejection_nonnegative P S _ _ _ _))
  · obtain ⟨hx,hy⟩ := hv
    have hxr := qa_of_decode (preGame P) (rows P) (referenceQuestion (rows P))
      (le_of_eq (CompilerApproxDecoder.reference_count (rows P))) (by simp [referenceQuestion]) x hx
    have hyc := qb_of_decode (preGame P) (rows P) (columnQuestion (rows P) r)
      (le_of_eq (CompilerApproxDecoder.column_count (rows P) r)) (by simp [columnQuestion]) y hy
    subst x; subst y; subst a; subst b
    obtain ⟨j,rfl⟩ := application_index P r hr
    apply le_trans _ (row_bound P hP R S hS j)
    rw [rowContribution_eq]
    exact le_add_of_nonneg_left (mul_nonneg (by positivity) (rejection_nonnegative P S _ _ _ _))

/-- Number of entries in the actual padded loss sum. This deliberately coarse
finite count avoids needing a sharp reindexing of the two application classes. -/
def eventCount (P : Presentation) : ℝ :=
  ∑ _x : QA (finalGame P).scenario,∑ _y : QB (finalGame P).scenario,
    ∑ _a : AA (finalGame P).scenario,∑ _b : BB (finalGame P).scenario,(1:ℝ)

def compilerConstant (P : Presentation) : ℝ := 2*eventCount P*(16*∑ i,baseWeight P i)

theorem constant_nonnegative (P : Presentation) : 0≤compilerConstant P := by
  have hw : 0≤∑ i,baseWeight P i := Finset.sum_nonneg (fun i hi => baseWeight_nonnegative P i)
  have hc : 0≤eventCount P := by unfold eventCount; positivity
  unfold compilerConstant
  positivity

theorem class_bound (P : Presentation) (hP : P.admissible) (R : StructuralRealization P)
    (S : NormalStrategy (finalGame P).scenario) (hS : HonestApplicationRows P R S)
    (c : TestClass) (hc : c=.applicationForward ∨ c=.applicationReverse) :
    classContribution P S c≤eventCount P*((16*∑ i,baseWeight P i)*energyTotal P R) := by
  have he : 0≤energyTotal P R := Finset.sum_nonneg (fun i hi => energy_nonnegative R.density _)
  have hw : 0≤∑ i,baseWeight P i := Finset.sum_nonneg (fun i hi => baseWeight_nonnegative P i)
  unfold classContribution
  simp only [eventCount,Finset.sum_mul,one_mul]
  apply Finset.sum_le_sum; intro x hx
  apply Finset.sum_le_sum; intro y hy
  apply Finset.sum_le_sum; intro a ha
  apply Finset.sum_le_sum; intro b hb
  by_cases ht : testClass P x y a b=c
  · simp only [ht,ite_true]
    apply application_event_bound P hP R S hS
    rcases hc with hc|hc
    · exact Or.inl (ht.trans hc)
    · exact Or.inr (ht.trans hc)
  · simp only [ht,ite_false,mul_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hw) he

/-- Explicit finite ApproxCompiled bound. The compilerConstant is conservative: it
counts all padded events and uses beta<=16 rather than optimizing a maximum. -/
theorem loss_bound (P : Presentation) (hP : P.admissible) (R : StructuralRealization P)
    (S : NormalStrategy (finalGame P).scenario) (hS : HonestApplicationRows P R S)
    (hz : classContribution P S .structural=0) (hp : classContribution P S .preGame=0) :
    loss (finalGame P) S≤compilerConstant P*((applicationResiduals P R).map (fun A =>
      (trace (R.density.op*(star A*A))).re)).sum := by
  have hf := class_bound P hP R S hS .applicationForward (Or.inl rfl)
  have hr := class_bound P hP R S hS .applicationReverse (Or.inr rfl)
  rw [← energyTotal_residuals]
  calc
    loss (finalGame P) S=classContribution P S .applicationForward+
        classContribution P S .applicationReverse := by rw [loss_decomposition,hz,hp]; ring
    _≤eventCount P*((16*∑ i,baseWeight P i)*energyTotal P R)+
        eventCount P*((16*∑ i,baseWeight P i)*energyTotal P R) := add_le_add hf hr
    _=compilerConstant P*energyTotal P R := by unfold compilerConstant; ring

/-- Precisely the strategy-assembly obligation left to the clock development. -/
def ClockObligation (P : Presentation) : Prop :=
  ∀ R : StructuralRealization P,∃ S : NormalStrategy (finalGame P).scenario,
    HonestApplicationRows P R S ∧ classContribution P S .structural=0 ∧
      classContribution P S .preGame=0

theorem approxCompiled_of_clock (P : Presentation) (hP : P.admissible) (H : ClockObligation P) :
    ApproxCompiled P (codeFor P) := by
  refine ⟨compilerConstant P,constant_nonnegative P,?_⟩
  intro G hG R
  have hg : finalGame P=G := Option.some.inj ((decode_codeFor P).symm.trans hG)
  subst G
  obtain ⟨S,hS,hz,hp⟩ := H R
  exact ⟨S,loss_bound P hP R S hS hz hp⟩

#print axioms application_shape
#print axioms application_event_bound
#print axioms constant_nonnegative
#print axioms class_bound
#print axioms loss_bound
#print axioms ClockObligation
#print axioms approxCompiled_of_clock
end Sigma2.CompilerApproxDictionaryEvents
