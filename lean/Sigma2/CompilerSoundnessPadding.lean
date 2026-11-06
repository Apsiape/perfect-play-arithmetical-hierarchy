import Sigma2.CompilerScaffold
import Sigma2.Compiler
import Sigma2.RowRestriction

/-! Normalize the actual padded FMS measurements by folding only unused answers
into the inactive answer. The submitted ensemble and every event probability
are preserved; no faithfulness on the whole ambient Hilbert space is assumed. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace Classical
namespace Sigma2.CompilerSoundnessPadding
open Compiler CompilerScaffold CoarseCells TensorLifts Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

abbrev Answer := Fin 12

def embed6 (a : Fin 6) : Answer := ⟨a.val,by have := a.isLt; omega⟩
def fold6 (a : Answer) : Fin 6 := if h : a.val<6 then ⟨a.val,h⟩ else 5
def foldFms (a : Answer) : Answer := embed6 (fold6 a)

def fold (q : Question) (a : Answer) : Answer :=
  match q with
  | .fms _ _ => foldFms a
  | _ => a

theorem fold_valid (q : Question) (a : Answer) (ha : valid q a.val=true) : fold q a=a := by
  cases q <;> try rfl
  simp only [valid,decide_eq_true_eq] at ha
  apply Fin.ext
  simp [fold,foldFms,fold6,embed6,ha]

def measurements (P : Presentation) (S : NormalStrategy (scenario P)) :
    Measurements (scenario P) :=
  TensorLifts.measurements (scenario P)
    (fun x a => coarse (S.measurements.alice x) (fold (question P x.val)) a)
    (fun y b => coarse (S.measurements.bob y) (fold (question P y.val)) b)
    (fun _ _ => coarse_positive _ _ _ (S.measurements.alice_pos _))
    (fun _ _ => coarse_positive _ _ _ (S.measurements.bob_pos _))
    (fun _ => (coarse_sum _ _).trans (S.measurements.alice_sum _))
    (fun _ => (coarse_sum _ _).trans (S.measurements.bob_sum _))

def normalize (P : Presentation) (S : NormalStrategy (scenario P)) :
    NormalStrategy (scenario P) where
  measurements := measurements P S
  vector := S.vector
  unit := S.unit
  weight := S.weight
  weight_nonneg := S.weight_nonneg
  weight_summable := S.weight_summable
  weight_sum := S.weight_sum

theorem component_probability (P : Presentation) (S : NormalStrategy (scenario P)) (k x y a b) :
    ((normalize P S).component k).probability x y a b =
      ∑ aa, ∑ bb, if fold (question P x.val) aa=a then
        if fold (question P y.val) bb=b then (S.component k).probability x y aa bb else 0 else 0 := by
  simp only [PureStrategy.probability,measurements_left,measurements_right]
  change (inner ℂ (S.vector k) ((left (coarse _ _ a)*right (coarse _ _ b)) (S.vector k))).re = _
  rw [RowRestriction.left_coarse,RowRestriction.right_coarse,Finset.sum_mul]
  simp only [Finset.mul_sum,sum_apply,inner_sum,complex_re_sum]
  apply Finset.sum_congr rfl
  intro aa _
  apply Finset.sum_congr rfl
  intro bb _
  split_ifs <;> simp_all [NormalStrategy.component]

theorem coarse_probability (P : Presentation) (S : NormalStrategy (scenario P)) (x y a b) :
    (normalize P S).probability x y a b =
      ∑ aa, ∑ bb, if fold (question P x.val) aa=a then
        if fold (question P y.val) bb=b then S.probability x y aa bb else 0 else 0 := by
  let f := fun aa bb k => S.weight k * (if fold (question P x.val) aa=a then
    if fold (question P y.val) bb=b then (S.component k).probability x y aa bb else 0 else 0)
  have hf aa bb : Summable (f aa bb) := by
    dsimp [f]
    split_ifs
    · exact event_summable S _ _ aa bb
    all_goals simp only [mul_zero]; exact summable_zero
  have hh : (normalize P S).probability x y a b=∑' k,∑ aa,∑ bb,f aa bb k := by
    unfold NormalStrategy.probability
    change (∑' k,S.weight k*((normalize P S).component k).probability x y a b)=_
    simp only [component_probability,Finset.mul_sum]
    rfl
  rw [hh,Summable.tsum_finsetSum (fun aa _ => summable_sum (fun bb _ => hf aa bb))]
  apply Finset.sum_congr rfl
  intro aa _
  rw [Summable.tsum_finsetSum (fun bb _ => hf aa bb)]
  apply Finset.sum_congr rfl
  intro bb _
  dsimp [f]
  split_ifs <;> simp [NormalStrategy.probability]

theorem invalid_probability (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (x y a b)
    (ha : valid (question P x.val) a.val=false ∨ valid (question P y.val) b.val=false) :
    S.probability x y a b=0 := by
  apply pre_rejected_probability P S hS
  change rule P _ _ _ _=false
  rcases ha with ha | hb
  · simp only [rule,ha,Bool.false_and]
  · simp only [rule,hb,Bool.and_false,Bool.false_and]

/-- Every probability of the original submitted strategy is preserved. -/
theorem probability (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (x y a b) :
    (normalize P S).probability x y a b=S.probability x y a b := by
  rw [coarse_probability]
  have ht (aa bb : Answer) :
      (if fold (question P x.val) aa=a then
        if fold (question P y.val) bb=b then S.probability x y aa bb else 0 else 0)=
      (if aa=a then if bb=b then S.probability x y aa bb else 0 else 0) := by
    by_cases ha : valid (question P x.val) aa.val=true
    · by_cases hb : valid (question P y.val) bb.val=true
      · rw [fold_valid _ _ ha,fold_valid _ _ hb]
      · rw [invalid_probability P S hS x y aa bb (Or.inr (Bool.eq_false_iff.mpr hb))]
        simp
    · rw [invalid_probability P S hS x y aa bb (Or.inl (Bool.eq_false_iff.mpr ha))]
      simp
  simp_rw [ht]
  simpa only [Finset.sum_ite_irrel,Finset.sum_ite_eq',Finset.mem_univ,ite_true,Finset.sum_const_zero]

theorem perfect_of_probability (G : Game) (S T : NormalStrategy G.scenario)
    (hp : ∀ x y a b,S.probability x y a b=T.probability x y a b)
    (hT : Perfect G T) : Perfect G S := by
  unfold Perfect loss at hT ⊢
  simpa only [hp] using hT

theorem perfect (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) : Perfect (preGame P) (normalize P S) :=
  perfect_of_probability (preGame P) (normalize P S) S (probability P S hS) hS

theorem coarse_fms (E : Answer → Op) (a : Fin 6) :
    coarse E foldFms (embed6 a)=coarse E fold6 a := by
  unfold coarse
  apply Finset.sum_congr rfl
  intro b _
  have he : foldFms b=embed6 a ↔ fold6 b=a := by
    simp only [foldFms,embed6,Fin.ext_iff]
  simp only [he]

theorem fms_sum (E : Answer → Op) (hE : ∑ a,E a=1) :
    (∑ a : Fin 6,coarse E foldFms (embed6 a))=1 := by
  simp_rw [coarse_fms]
  exact (coarse_sum E fold6).trans hE

/-- All four concrete six-answer instances are normalized, including the
inactive answer. This uses the actual pre-game, not an assumed FMS supplier. -/
theorem conditionalPerfect (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (g : Fin 4) :
    ConditionalPerfect (normalize P S) (fmsInstance P g) := by
  refine ⟨?_,?_,?_⟩
  · intro x y a b hr
    rw [probability P S hS]
    apply pre_rejected_probability P S hS
    rw [pre_fms_rule]
    exact hr
  · intro x
    change (∑ a : Fin 6,coarse (S.measurements.alice ((fmsInstance P g).qA x))
      (fold (question P ((names P).length+5*g.val+x.val))) (embed6 a))=1
    rw [question_fms]
    exact fms_sum _ (S.measurements.alice_sum _)
  · intro y
    change (∑ b : Fin 6,coarse (S.measurements.bob ((fmsInstance P g).qB y))
      (fold (question P ((names P).length+5*g.val+y.val))) (embed6 b))=1
    rw [question_fms]
    exact fms_sum _ (S.measurements.bob_sum _)

theorem fms_effect (E : Answer → Op) (a : Answer) (ha : a.val<5) :
    coarse E foldFms a=E a := by
  unfold coarse
  have he (b : Answer) : foldFms b=a ↔ b=a := by
    by_cases hb : b.val<6
    · simp only [foldFms,fold6,hb,dite_true,embed6]
    · have hn : ¬ embed6 (5:Fin 6)=a := by intro hh; have hv := congrArg Fin.val hh; simp only [embed6] at hv; omega
      have hba : b≠a := by intro hh; subst b; omega
      simp only [foldFms,fold6,hb,dite_false,hn,hba]
  simp only [he]
  simp

/-- The actual calibrated flag and four magic blocks are untouched globally. -/
theorem flag_eq (P : Presentation) (S : NormalStrategy (scenario P)) (g : Fin 4) :
    flagA (normalize P S) (fmsInstance P g)=flagA S (fmsInstance P g) := by
  change coarse _ (fold (question P ((names P).length+5*g.val+(0:Fin 5).val))) _=_
  rw [question_fms]
  exact fms_effect _ _ (by change (0:ℕ)<5; decide)

theorem magic_eq (P : Presentation) (S : NormalStrategy (scenario P)) (g : Fin 4) (i : Fin 4) :
    magicA (normalize P S) (fmsInstance P g) i=magicA S (fmsInstance P g) i := by
  unfold magicA
  split_ifs with hi
  · change coarse _ (fold (question P ((names P).length+5*g.val+(4:Fin 5).val))) _=_
    rw [question_fms]
    exact fms_effect _ _ (by change (2:ℕ)<5; decide)
  · change coarse _ (fold (question P ((names P).length+5*g.val+(3:Fin 5).val))) _=_
    rw [question_fms]
    exact fms_effect _ _ (by have := i.isLt; change i.val+1<5; omega)

theorem alice_fms_effect (P : Presentation) (S : NormalStrategy (scenario P)) (g : Fin 4)
    (x : Fin 5) (a : Fin 6) (ha : a.val<5) :
    (normalize P S).measurements.alice ((fmsInstance P g).qA x) ((fmsInstance P g).aA a)=
      S.measurements.alice ((fmsInstance P g).qA x) ((fmsInstance P g).aA a) := by
  change coarse _ (fold (question P ((names P).length+5*g.val+x.val))) _=_
  rw [question_fms]
  exact fms_effect _ _ ha

theorem transport_eq (P : Presentation) (S : NormalStrategy (scenario P)) (g : Fin 4) :
    transportA (normalize P S) (fmsInstance P g)=transportA S (fmsInstance P g) := by
  simp only [transportA,magic_eq,flag_eq,
    alice_fms_effect P S g 3 0 (by decide),alice_fms_effect P S g 3 1 (by decide)]

theorem marginalA (P : Presentation) (S : NormalStrategy (scenario P)) (h : Density) :
    MarginalA (normalize P S) h ↔ MarginalA S h := Iff.rfl

theorem marginalB (P : Presentation) (S : NormalStrategy (scenario P)) (h : Density) :
    MarginalB (normalize P S) h ↔ MarginalB S h := Iff.rfl

theorem entropy (P : Presentation) (S : NormalStrategy (scenario P)) :
    FiniteMarginalEntropy (normalize P S) ↔ FiniteMarginalEntropy S := Iff.rfl

/-- Lemma 4.1 now applies to the original concrete scaffold operators. -/
theorem actual_bridge (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (g : Fin 4) (h : Density)
    (hm : MarginalA S h) (e : Op) (he : SupportOf h e) :
    BridgeConclusion S (fmsInstance P g) h e := by
  have hh := ActualCalibration.actual_normal_bridge (normalize P S) (fmsInstance P g)
    (conditionalPerfect P S hS g) h hm e he
  simpa only [BridgeConclusion,flag_eq,magic_eq,transport_eq] using hh

#print axioms probability
#print axioms conditionalPerfect
#print axioms flag_eq
#print axioms magic_eq
#print axioms transport_eq
#print axioms actual_bridge
end Sigma2.CompilerSoundnessPadding
