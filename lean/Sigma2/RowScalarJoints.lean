import Sigma2.RowScalar

noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.RowScalar
open Compiler RowGame TensorLifts Preliminaries CoarseCells FiniteSpectral

def binary (G : Game) (R : Rows G.scenario) (M : Measurements (scenario G R))
    (P : Op) (q : NewQ R) : Op :=
  signed (compressed P (M.alice (qa G R q))) (fun a => binaryClass a.val)

theorem diagonal_reject {s} (R : Rows s) (q : Q R) (f : ℕ → Fin 4) (a b : ℕ)
    (hne : f a≠f b) : newRule R q q a b=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  simp only [newRule,Bool.and_eq_true,ite_true,decide_eq_true_eq] at hh
  exact hne (congrArg f hh.1.1.2)

/-- The finite rejection predicate supplies the hypotheses of support matching. -/
theorem bound_analysis (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (q p : NewQ R) (f u : ℕ → Fin 4)
    (hz : ∀ a b,f a≠u b → newRule R q.val p.val a b=false) (t : Fin 4) :
    left (coarse (S.measurements.alice (qa G R q)) (fun a => f a.val) t) S.vector=
      right (coarse (S.measurements.bob (qb G R p)) (fun b => u b.val) t) S.vector ∧
    Projection (coarse (compressed P (S.measurements.alice (qa G R q))) (fun a => f a.val) t) := by
  have hh := coarse_analysis S h hm P hP
    (S.measurements.alice (qa G R q)) (S.measurements.bob (qb G R p))
    (S.measurements.alice_pos _) (S.measurements.bob_pos _)
    (S.measurements.alice_sum _) (S.measurements.bob_sum _)
    (fun a => f a.val) (fun b => u b.val) ?_ t
  · exact ⟨hh.1,by rw [coarse_compressed]; exact hh.2.2.1⟩
  · intro a b hab
    have hh := rejected_probability G R (normalOfPure S) hS (qa G R q) (qb G R p) a b ?_
    · rw [normalOfPure_probability] at hh
      simpa only [PureStrategy.probability,measurements_left,measurements_right] using hh
    · change accepts G R _ _ _ _=false
      simp only [accepts,decode_qa,decode_qb]
      exact hz a.val b.val hab

/-- A context's signed marginal equals the actual synchronized binary cell,
not merely some abstract Pauli observable. -/
theorem bound_signed (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (q p : NewQ R) (f : ℕ → Fin 4)
    (hz : ∀ a b,f a≠binaryClass b → newRule R q.val p.val a b=false) :
    signed (compressed P (S.measurements.alice (qa G R q))) (fun a => f a.val)=
      binary G R S.measurements P p := by
  obtain ⟨_,hB,_,hmB⟩ := marginals_exist (normalOfPure S)
  obtain ⟨Q,hQ⟩ := support_exists hB
  have he (t : Fin 4) :
      coarse (compressed P (S.measurements.alice (qa G R q))) (fun a => f a.val) t=
      coarse (compressed P (S.measurements.alice (qa G R p))) (fun a => binaryClass a.val) t := by
    rw [coarse_compressed,coarse_compressed]
    apply MirrorAlgebra.local_eq S h hm P hP
    · simp only [mul_assoc,hP.1.2]
    · simp only [mul_assoc,hP.1.2]
    · have hq := MirrorAlgebra.compressed_mirror S.vector P Q _ _
        (MirrorAlgebra.left_support S h hm P hP) (MirrorAlgebra.right_support S hB hmB Q hQ)
        (bound_analysis G R S hS h hm P hP q p f binaryClass hz t).1
      have hp := MirrorAlgebra.compressed_mirror S.vector P Q _ _
        (MirrorAlgebra.left_support S h hm P hP) (MirrorAlgebra.right_support S hB hmB Q hQ)
        (bound_analysis G R S hS h hm P hP p p binaryClass binaryClass
          (diagonal_reject R p.val binaryClass) t).1
      exact hq.trans hp.symm
  exact congrArg₂ (fun A B : Op => A-B) (he 1) (he 2)

/-- Each square observable is its measured synchronized cell on the support. -/
theorem pure_cells_identify (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) (x y : Fin 3) :
    cells G R S.measurements P g x y=binary G R S.measurements P (cellQ R g x y) := by
  exact bound_signed G R S hS h hm P hP (lineQ R g false x) (cellQ R g x y)
    (contextClass false y) (context_reject R g false x y)

def axisQ {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) : NewQ R :=
  if k=0 then cellQ R g 0 0 else if k=1 then cellQ R g 1 0
  else if k=2 then cellQ R g 1 1 else cellQ R g 0 1

@[simp] theorem axisQ_val {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) :
    (axisQ R g k).val=axis R g k := by unfold axisQ axis; split_ifs <;> rfl

def crossQ {s} (R : Rows s) (g h : Fin (RowSlots.squares R)) (k l : Fin 4) : NewQ R :=
  ⟨.cross g h k l, by simp [questions,List.mem_flatMap,List.mem_map]⟩

theorem cross_reject {s} (R : Rows s) (g h : Fin (RowSlots.squares R)) (hgh : g≠h)
    (k l : Fin 4) (first : Bool) (a b : ℕ)
    (hne : binaryClass (if first then a/2 else a%2)≠binaryClass b) :
    newRule R (.cross g h k l) (if first then axis R g k else axis R h l) a b=false := by
  apply Bool.eq_false_iff.mpr
  intro hh
  have hd : directed R (.cross g h k l) (if first then axis R g k else axis R h l) a b=true := by
    simp only [newRule,Bool.and_eq_true] at hh
    exact hh.1.2
  simp only [directed,hgh,ite_false,Bool.and_eq_true] at hd
  cases first
  · have he : b=a%2 := by simpa using hd.2
    exact hne (by simp [he])
  · have he : b=a/2 := by simpa using hd.1
    exact hne (by simp [he])

/-- Four-answer cross-square joints force actual scalar axes to commute.
This is compiler.tex (N6d), in Lemma 4.3's scalar-algebra subsection. -/
theorem pure_cross_commute (G : Game) (R : Rows G.scenario)
    (S : PureStrategy (scenario G R)) (hS : Perfect (game G R) (normalOfPure S))
    (h : Density) (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P)
    (g u : Fin (RowSlots.squares R)) (hgu : g≠u) (k l : Fin 4) :
    Commute (binary G R S.measurements P (axisQ R g k))
      (binary G R S.measurements P (axisQ R u l)) := by
  let q := crossQ R g u k l
  have hz1 (a b) (hab : binaryClass (a/2)≠binaryClass b) :
      newRule R q.val (axisQ R g k).val a b=false := by
    simpa only [q,crossQ,axisQ_val,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false] using cross_reject R g u hgu k l true a b hab
  have hz2 (a b) (hab : binaryClass (a%2)≠binaryClass b) :
      newRule R q.val (axisQ R u l).val a b=false := by
    simpa only [q,crossQ,axisQ_val,Bool.true_eq,ite_true,Bool.false_eq_true,ite_false] using cross_reject R g u hgu k l false a b hab
  have he1 := bound_signed G R S hS h hm P hP q (axisQ R g k) (fun a => binaryClass (a/2)) hz1
  have he2 := bound_signed G R S hS h hm P hP q (axisQ R u l) (fun a => binaryClass (a%2)) hz2
  rw [← he1,← he2]
  exact signed_commute _ _ _ P hP.1
    (compressed_positive P hP.1 _ (S.measurements.alice_pos _))
    (compressed_sum P hP.1 _ (S.measurements.alice_sum _))
    (fun t => (bound_analysis G R S hS h hm P hP q (axisQ R g k) _ _ hz1 t).2)
    (fun t => (bound_analysis G R S hS h hm P hP q (axisQ R u l) _ _ hz2 t).2)



theorem pure_perfect_transfer (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (T : PureStrategy (scenario G R))
    (hp : ∀ x y a b,S.probability x y a b=T.probability x y a b) :
    Perfect (game G R) (normalOfPure T) := by
  have he : loss (game G R) (normalOfPure T)=loss (game G R) S := by
    dsimp only [loss,game]
    simp_rw [normalOfPure_probability,← hp]
  exact he.trans hS

/-- Cell identification holds for the unchanged Alice operators of a mixed state. -/
theorem cells_identify (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) (x y : Fin 3) :
    cells G R S.measurements P g x y=binary G R S.measurements P (cellQ R g x y) := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  have hh := pure_cells_identify G R T (pure_perfect_transfer G R S hS T hprob)
    h (hM h hm) P hP g x y
  simpa only [cells,context,binary,hA] using hh

/-- Actual cross-square commutation, including mixed normal strategies. -/
theorem cross_commute (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g u : Fin (RowSlots.squares R)) (hgu : g≠u) (k l : Fin 4) :
    Commute (binary G R S.measurements P (axisQ R g k))
      (binary G R S.measurements P (axisQ R u l)) := by
  obtain ⟨T,hA,_,hM,hprob⟩ := PureTransfer.preserving_alice S
  have hh := pure_cross_commute G R T (pure_perfect_transfer G R S hS T hprob)
    h (hM h hm) P hP g u hgu k l
  simpa only [binary,hA] using hh

/-- The Pauli relations refer to the actual four measured scalar axes. -/
theorem measured_pauli_pairs (G : Game) (R : Rows G.scenario)
    (S : NormalStrategy (scenario G R)) (hS : Perfect (game G R) S)
    (h : Density) (hm : MarginalA S h) (P : Op) (hP : SupportOf h P)
    (g : Fin (RowSlots.squares R)) :
    FourUnits.TwoPairs P (binary G R S.measurements P (axisQ R g 2))
      (binary G R S.measurements P (axisQ R g 0))
      (binary G R S.measurements P (axisQ R g 3))
      (binary G R S.measurements P (axisQ R g 1)) := by
  have hh := pauli_pairs G R S hS h hm P hP g
  dsimp only at hh
  simpa only [cells_identify G R S hS h hm P hP,axisQ,ite_true,
    show (1:Fin 4)≠0 by decide,show (2:Fin 4)≠0 by decide,
    show (2:Fin 4)≠1 by decide,show (3:Fin 4)≠0 by decide,
    show (3:Fin 4)≠1 by decide,show (3:Fin 4)≠2 by decide,ite_false] using hh

#print axioms pure_cells_identify
#print axioms cells_identify
#print axioms cross_commute
#print axioms measured_pauli_pairs
end Sigma2.RowScalar

