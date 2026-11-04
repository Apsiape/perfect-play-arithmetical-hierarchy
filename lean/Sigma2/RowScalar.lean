import Sigma2.RowGame
import Sigma2.FourUnits
import Sigma2.PureTransfer

/-! Lemma 4.3, "A certified scalar matrix algebra": extraction from the
actual Boolean contexts. All identities below are on the supplied state support.
The support and matching arguments are compiler.tex (N3)--(N6), as also used
in the entropy paper's Theorem B; no paper result is assumed as an axiom. -/
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame TensorLifts Preliminaries CoarseCells FiniteSpectral

abbrev NewQ {s} (R : Rows s) := {q : Q R // q ∈ questions R}

def qa (G : Game) (R : Rows G.scenario) (q : NewQ R) : QA (scenario G R) :=
  ⟨G.scenario.questionsA+1+(questions R).idxOf q.val, by
    have := List.idxOf_lt_length_of_mem q.property
    dsimp [scenario]; omega⟩

def qb (G : Game) (R : Rows G.scenario) (q : NewQ R) : QB (scenario G R) :=
  ⟨G.scenario.questionsB+1+(questions R).idxOf q.val, by
    have := List.idxOf_lt_length_of_mem q.property
    dsimp [scenario]; omega⟩

@[simp] theorem decode_qa (G : Game) (R : Rows G.scenario) (q : NewQ R) :
    decodeA G R (qa G R q)=.inr q.val := by
  simp [decodeA,qa,List.getElem?_idxOf q.property] <;> omega

@[simp] theorem decode_qb (G : Game) (R : Rows G.scenario) (q : NewQ R) :
    decodeB G R (qb G R q)=.inr q.val := by
  simp [decodeB,qb,List.getElem?_idxOf q.property] <;> omega

def cellQ {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (x y : Fin 3) : NewQ R :=
  ⟨.cell g x y, by simp [questions,List.mem_flatMap,List.mem_map] <;> aesop⟩

def lineQ {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (col : Bool) (k : Fin 3) : NewQ R :=
  ⟨.line g col k, by simp [questions,List.mem_flatMap,List.mem_map]; cases col <;> aesop⟩

/-- The accepted rule is read at the actual embedded questions. -/
theorem accepts_new (G : Game) (R : Rows G.scenario) (q p : NewQ R) (a b) :
    (game G R).accepts (qa G R q) (qb G R p) a b=newRule R q.val p.val a.val b.val := by
  change accepts G R _ _ _ _=_
  simp only [accepts,decode_qa,decode_qb]

/-- Positive class 1 and negative class 2, with no flag or inactive sector. -/
def binaryClass (a : ℕ) : Fin 4 := if a=1 then 1 else 2

def contextClass (neg : Bool) (j : Fin 3) (a : ℕ) : Fin 4 :=
  if cellSign neg (a%4) j.val then 2 else 1

/-- Every context coarse marginal is bound by the actual predicate to its cell. -/
theorem context_reject {s} (R : Rows s) (g : Fin (RowSlots.squares R))
    (col : Bool) (k j : Fin 3) (a b : ℕ)
    (hne : contextClass (col && decide (k.val=2)) j a ≠ binaryClass b) :
    newRule R (.line g col k) (if col then .cell g j k else .cell g k j) a b=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  simp only [newRule,Bool.and_eq_true] at hh
  have hv : valid R (.line g col k) a=true := hh.1.1.1.1
  have ha : a<4 := by simpa [valid] using hv
  have hd : directed R (.line g col k) (if col then .cell g j k else .cell g k j) a b=true := by
    exact hh.1.2
  simp only [directed,List.all_eq_true,List.mem_finRange] at hd
  have hj := hd j (by simp)
  simp only [ite_true,decide_eq_true_eq] at hj
  subst b
  apply hne
  rw [contextClass,Nat.mod_eq_of_lt ha]
  cases hs : cellSign (col && decide (k.val=2)) a j.val <;> simp [bitAnswer,binaryClass,hs]

/-- Pure-state extraction for every context and every coarse class. -/
theorem context_analysis (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) (col : Bool) (k j : Fin 3) (t : Fin 4) :
    let A := S.measurements.alice (qa G R (lineQ R g col k))
    let B := S.measurements.bob (qb G R (cellQ R g (if col then j else k) (if col then k else j)))
    let p := fun a : AA (scenario G R) => contextClass (col && decide (k.val=2)) j a.val
    let q := fun b : BB (scenario G R) => binaryClass b.val
    left (coarse A p t) S.vector=right (coarse B q t) S.vector ∧
      coarse A p t*P=P*coarse A p t ∧ Projection (P*coarse A p t*P) ∧
      Centralizes h.op (coarse A p t) := by
  dsimp only
  apply coarse_analysis S h hm P hP _ _
    (S.measurements.alice_pos _) (S.measurements.bob_pos _)
    (S.measurements.alice_sum _) (S.measurements.bob_sum _)
  intro a b hab
  have hz := rejected_probability G R (normalOfPure S) hS
    (qa G R (lineQ R g col k))
    (qb G R (cellQ R g (if col then j else k) (if col then k else j))) a b ?_
  · rw [normalOfPure_probability] at hz
    simpa only [PureStrategy.probability,measurements_left,measurements_right] using hz
  · change accepts G R _ _ _ _=false
    simp only [accepts,decode_qa,decode_qb]
    cases col <;> exact context_reject R g _ k j a.val b.val hab




def context (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P : Op) (g : Fin (RowSlots.squares R)) (col : Bool) (k j : Fin 3) : Op :=
  signed (compressed P (M.alice (qa G R (lineQ R g col k))))
    (fun a => contextClass (col && decide (k.val=2)) j a.val)

def cells (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P : Op) (g : Fin (RowSlots.squares R)) (x y : Fin 3) : Op :=
  context G R M P g false x y

/-- Sharp marginals on the same supplied support; no full-space projectivity
of the original POVM is assumed. -/
theorem context_sharp (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) (col : Bool) (k j : Fin 3) (t : Fin 4) :
    Projection (coarse (compressed P (S.measurements.alice (qa G R (lineQ R g col k))))
      (fun a => contextClass (col && decide (k.val=2)) j a.val) t) := by
  rw [coarse_compressed]
  exact (context_analysis G R S hS h hm P hP g col k j t).2.2.1

/-- Both occurrences of a cell are identified by their common opposite
binary cell, using dense-range cancellation on the original support. -/
theorem context_equal (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) (x y : Fin 3) :
    cells G R S.measurements P g x y=context G R S.measurements P g true y x := by
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  have he (t : Fin 4) :
      coarse (compressed P (S.measurements.alice (qa G R (lineQ R g false x))))
        (fun a => contextClass (false && decide (x.val=2)) y a.val) t =
      coarse (compressed P (S.measurements.alice (qa G R (lineQ R g true y))))
        (fun a => contextClass (true && decide (y.val=2)) x a.val) t := by
    rw [coarse_compressed,coarse_compressed]
    apply MirrorAlgebra.local_eq S h hm P hP
    · simp only [mul_assoc,hP.1.2]
    · simp only [mul_assoc,hP.1.2]
    · have hr := MirrorAlgebra.compressed_mirror S.vector P Q _ _
        (MirrorAlgebra.left_support S h hm P hP)
        (MirrorAlgebra.right_support S hB hmB Q hQ)
        (context_analysis G R S hS h hm P hP g false x y t).1
      have hc := MirrorAlgebra.compressed_mirror S.vector P Q _ _
        (MirrorAlgebra.left_support S h hm P hP)
        (MirrorAlgebra.right_support S hB hmB Q hQ)
        (context_analysis G R S hS h hm P hP g true y x t).1
      exact hr.trans hc.symm
  exact congrArg₂ (fun A B : Op => A-B) (he 1) (he 2)

theorem value_sq (neg : Bool) (j : Fin 3) (a : ℕ) :
    signValue (contextClass neg j a)*signValue (contextClass neg j a)=1 := by
  unfold contextClass
  split <;> norm_num [signValue]

theorem value_product (neg : Bool) (a : ℕ) :
    signValue (contextClass neg 2 a)*signValue (contextClass neg 1 a)*
      signValue (contextClass neg 0 a)=(if neg then (-1:ℂ) else 1) := by
  have ha : a%4<4 := Nat.mod_lt _ (by omega)
  generalize hv : a%4=v at *
  interval_cases v <;> cases neg <;> norm_num [contextClass,hv,cellSign,signValue]

theorem context_square {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Op) (v : ι → ℕ) (neg : Bool) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hp : ∀ j t,Projection (coarse B (fun a => contextClass neg j (v a)) t)) (j : Fin 3) :
    signed B (fun a => contextClass neg j (v a))*signed B (fun a => contextClass neg j (v a))=P := by
  conv_lhs => rhs; rw [signed_eq_weighted]
  rw [signed_weighted B _ P hP hB hs (hp j)]
  simpa only [weighted,value_sq,one_smul] using hs

theorem context_product {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Op) (v : ι → ℕ) (neg : Bool) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (hp : ∀ j t,Projection (coarse B (fun a => contextClass neg j (v a)) t)) :
    signed B (fun a => contextClass neg 0 (v a))*
      (signed B (fun a => contextClass neg 1 (v a))*signed B (fun a => contextClass neg 2 (v a)))=
        (if neg then (-1:ℂ) else 1) • P := by
  rw [signed_eq_weighted B (fun a => contextClass neg 2 (v a)),
    signed_weighted B _ P hP hB hs (hp 1),
    signed_weighted B _ P hP hB hs (hp 0)]
  simp only [weighted,value_product,← Finset.smul_sum,hs]

/-- The nine concrete context observables satisfy every square relation.
This discharges the scalar Pauli-relation extraction subobligation of turn 11,
formalizing the unflagged calculation in Lemma 4.3 and entropy Theorem B. -/
theorem pure_square_relations (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) :
    PauliExtraction.SquareRelations P (cells G R S.measurements P g) := by
  have hp := context_sharp G R S hS h hm P hP g
  have hpos (col k) := compressed_positive P hP.1
    (S.measurements.alice (qa G R (lineQ R g col k))) (S.measurements.alice_pos _)
  have hsum (col k) := compressed_sum P hP.1
    (S.measurements.alice (qa G R (lineQ R g col k))) (S.measurements.alice_sum _)
  have he := context_equal G R S hS h hm P hP g
  have hr (col k j) : context G R S.measurements P g col k j*P=
      context G R S.measurements P g col k j :=
    MagicRelations.signed_supported P hP.1 _ _
  have hs (col k j) : star (context G R S.measurements P g col k j)=
      context G R S.measurements P g col k j := signed_selfadjoint _ _ (hp col k j)
  have hsq (col k j) : context G R S.measurements P g col k j*
      context G R S.measurements P g col k j=P :=
    context_square _ Fin.val _ P hP.1 (hpos col k) (hsum col k) (hp col k) j
  refine ⟨hP.1,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro x y; exact hs false x y
  · intro x y; exact hr false x y
  · intro x y
    have hh := congrArg star (hr false x y)
    simpa only [star_mul,hP.1.1,hs,cells] using hh
  · intro x y; exact hsq false x y
  · intro x y z
    exact signed_commute _ _ _ P hP.1 (hpos false x) (hsum false x) (hp false x y) (hp false x z)
  · intro x z y
    rw [he x y,he z y]
    exact signed_commute _ _ _ P hP.1 (hpos true y) (hsum true y) (hp true y x) (hp true y z)
  · intro x
    simpa only [cells,context,Bool.false_and,Bool.false_eq_true,ite_false,one_smul] using
      context_product _ Fin.val false P hP.1 (hpos false x) (hsum false x) (hp false x)
  · intro y
    rw [he 0 y,he 1 y,he 2 y]
    simpa only [context,Bool.true_and,decide_eq_true_eq] using
      context_product _ Fin.val (decide (y.val=2)) P hP.1
      (hpos true y) (hsum true y) (hp true y)



/-- The original normal strategy's Alice operators and marginal are preserved
by purification. This is an operator identity on its actual support. -/
theorem square_relations (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) :
    PauliExtraction.SquareRelations P (cells G R S.measurements P g) := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  have ht : Perfect (game G R) (normalOfPure T) := by
    have he : loss (game G R) (normalOfPure T)=loss (game G R) S := by
      dsimp only [loss,game]
      simp_rw [normalOfPure_probability,← hprob]
    exact he.trans hS
  have hh := pure_square_relations G R T ht h (hM h hm) P hP g
  have he : cells G R T.measurements P g=cells G R S.measurements P g := by
    funext x y
    dsimp only [cells,context]
    rw [hA]
  rwa [he] at hh

/-- Both Pauli pairs and all four cross-pair commutators, obtained from
perfect play of the concrete turn-10 game, with no geometric hypothesis. -/
theorem pauli_pairs (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) :
    let C := cells G R S.measurements P g
    FourUnits.TwoPairs P (C 1 1) (C 0 0) (C 0 1) (C 1 0) := by
  have r := square_relations G R S hS h hm P hP g
  have ha := PauliExtraction.anticommute _ _ r
  refine ⟨?_,?_,r.col_commute 1 0 1,r.row_commute 1 1 0,
    r.row_commute 0 0 1,r.col_commute 0 1 0⟩
  · refine ⟨r.projection,r.selfadjoint 1 1,r.selfadjoint 0 0,r.right_unit 1 1,r.left_unit 1 1,
      r.right_unit 0 0,r.left_unit 0 0,r.square 1 1,r.square 0 0,?_⟩
    rw [ha.1,neg_neg]
  · exact ⟨r.projection,r.selfadjoint 0 1,r.selfadjoint 1 0,r.right_unit 0 1,r.left_unit 0 1,
      r.right_unit 1 0,r.left_unit 1 0,r.square 0 1,r.square 1 0,ha.2⟩

/-- Explicit M4 units for each scalar square on the original normal support. -/
theorem matrix_units (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) :
    let C := cells G R S.measurements P g
    let t := FourUnits.matrixUnit P (C 1 1) (C 0 0) (C 0 1) (C 1 0)
    (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
      (∀ i j,star (t i j)=t j i) ∧ (∑ i,t i i)=P := by
  have hp := pauli_pairs G R S hS h hm P hP g
  exact ⟨FourUnits.matrix_product _ _ _ _ _ hp,
    FourUnits.matrix_star _ _ _ _ _ hp,FourUnits.matrix_sum _ _ _ _ _ hp⟩

#print axioms context_analysis
#print axioms pure_square_relations
#print axioms square_relations
#print axioms pauli_pairs
#print axioms matrix_units
end Sigma2.RowScalar

