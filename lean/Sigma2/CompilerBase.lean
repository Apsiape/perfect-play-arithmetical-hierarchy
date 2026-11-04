import Sigma2.Preliminaries
import Sigma2.CompilerAlgebra
import Sigma2.ProjectionGraph
import Sigma2.DensityContraction

noncomputable section
open scoped BigOperators
namespace Sigma2

inductive LabelType where
  | unitary | projection | positive | contraction
  deriving DecidableEq, Repr, Encodable

inductive Expr where
  | scalar (q : ℚ)
  | label (i : ℕ)
  | add (p q : Expr)
  | mul (p q : Expr)
  | adj (p : Expr)
  deriving DecidableEq, Repr, Encodable

def Expr.eval (I : Op) (L : ℕ → Op) : Expr → Op
  | .scalar q => (q : ℂ) • I
  | .label i => L i
  | .add p q => p.eval I L + q.eval I L
  | .mul p q => p.eval I L * q.eval I L
  | .adj p => star (p.eval I L)

def Expr.labels : Expr → List ℕ
  | .scalar _ => []
  | .label i => [i]
  | .add p q | .mul p q => p.labels ++ q.labels
  | .adj p => p.labels

/-- Central polynomials and endpoint sums are separate syntax classes. No
centralizer word contains a modular transport or two creation operators. -/
structure Presentation where
  types : List LabelType
  root : ℕ
  transported : List ℕ
  central : List Expr
  endpoints : List (Expr × Fin 4 × Fin 4 × Expr)
  zeros : List (Expr × Fin 4)
  linear : List (List (Expr × Fin 4 × Expr))
  deriving DecidableEq, Repr, Encodable

def Presentation.admissible (P : Presentation) : Prop :=
  P.types[P.root]? = some .projection ∧
  (∀ i ∈ P.transported, i < P.types.length) ∧
  (∀ p ∈ P.central, ∀ i ∈ p.labels, i < P.types.length) ∧
  (∀ r ∈ P.endpoints, (∀ i ∈ r.1.labels, i ∈ P.transported) ∧
    (∀ i ∈ r.2.2.2.labels, i < P.types.length)) ∧
  (∀ r ∈ P.zeros, ∀ i ∈ r.1.labels, i ∈ P.transported) ∧
  (∀ row ∈ P.linear, ∀ r ∈ row,
    (∀ i ∈ r.1.labels, i < P.types.length) ∧
    (∀ i ∈ r.2.2.labels, i < P.types.length))

def TypedAt (e T : Op) : LabelType → Prop
  | .unitary => star T*T=e ∧ T*star T=e
  | .projection => Projection T
  | .positive => Positive T ∧ Positive (e-T)
  | .contraction => Contraction T

/-- A nonzero closed support in l2(N), with faithful trace-one density there.
Using a support projection also covers finite-dimensional extracted corners. -/
structure NormalRealization (P : Presentation) where
  support : Op
  support_projection : Projection support
  density : Density
  density_supported : support*density.op=density.op
  faithful_on : ∀ v, support v=v → density.op v=0 → v=0
  label : ℕ → Op
  creation : Fin 4 → Op
  label_supported : ∀ i, support*label i=label i ∧ label i*support=label i
  creation_supported : ∀ a, support*creation a=creation a ∧ creation a*support=creation a
  typed : ∀ i : Fin P.types.length, TypedAt support (label i.val) (P.types[i.val])
  centralizer : ∀ i, Centralizes density.op (label i)
  isometries : ∀ a b, star (creation a)*creation b = if a=b then support else 0
  ranges : ∑ a, creation a*star (creation a)=support-label P.root
  modular : ∀ a, density.op*creation a=(1/16:ℂ) • (creation a*density.op)
  central_equations : ∀ p ∈ P.central, p.eval support label=0
  endpoint_equations : ∀ r ∈ P.endpoints,
    r.1.eval support label * creation r.2.1 = creation r.2.2.1 * r.2.2.2.eval support label
  zero_equations : ∀ r ∈ P.zeros, r.1.eval support label * creation r.2=0
  linear_equations : ∀ row ∈ P.linear,
    (row.map (fun r => r.1.eval support label * creation r.2.1 * r.2.2.eval support label)).sum=0

def FiniteRealization {P} (R : NormalRealization P) : Prop :=
  FiniteDimensional ℂ (LinearMap.range R.support.toLinearMap)

def RealizationFiniteEntropy {P} (R : NormalRealization P) : Prop :=
  FiniteDensityEntropy R.density

end Sigma2

namespace Sigma2.Compiler

theorem projection_compl (P : Op) (hP : Projection P) : Projection (1-P) := by
  constructor
  · exact (star_sub _ _).trans (congrArg₂ (fun X Y : Op => X-Y) (star_one Op) hP.1)
  · simp only [sub_mul, mul_sub, one_mul, mul_one, hP.2]; abel

theorem projection_product (P Q : Op) (hP : Projection P) (hQ : Projection Q)
    (hc : P*Q=Q*P) : Projection (P*Q) := by
  constructor
  · rw [star_mul,hP.1,hQ.1,hc]
  · calc
      _ = P*(Q*P)*Q := by noncomm_ring
      _ = (P*P)*(Q*Q) := by rw [← hc]; noncomm_ring
      _ = P*Q := by rw [hP.2,hQ.2]



def cellSign (negativeParity : Bool) (v j : ℕ) : Bool :=
  if j=0 then decide (v/2%2=1) else if j=1 then decide (v%2=1)
  else Bool.xor (Bool.xor (decide (v/2%2=1)) (decide (v%2=1))) negativeParity

def retained (x k : ℕ) : ℕ := if k<x then k else k+1

/-- Full 5-by-5 FMS predicate, Section 4.1. Answer 0 is a row/column
flag; T/B answers 0,1 are signs and 2,3,4 are retained triples. -/
def fmsRule (x y a b : ℕ) : Bool :=
  if x<3 ∧ y<3 then
    if a=0 ∨ b=0 then decide (a=0 ∧ b=0)
    else decide (cellSign false (a-1) y = cellSign (decide (y=2)) (b-1) x)
  else if 3≤x ∧ y=0 then
    if a<2 then decide (b=0 ∨ b=x-2)
    else decide (b=retained (x-3) (a-2)+1)
  else if x=0 ∧ 3≤y then
    if b<2 then decide (a=0 ∨ a=y-2)
    else decide (a=retained (y-3) (b-2)+1)
  else if 3≤x ∧ 3≤y ∧ a<2 ∧ b<2 then
    decide ((a+b)%2=((x-3)*(y-3))%2)
  else true

def conditionalFmsRule (x y a b : ℕ) : Bool :=
  if a=5 ∨ b=5 then decide (a=5 ∧ b=5) else fmsRule x y a b

structure FMSInstance (s : Scenario) where
  qA : Fin 5 → QA s
  qB : Fin 5 → QB s
  aA : Fin 6 → AA s
  aB : Fin 6 → BB s
  qA_injective : Function.Injective qA
  qB_injective : Function.Injective qB
  aA_injective : Function.Injective aA
  aB_injective : Function.Injective aB

def ConditionalPerfect {s} (S : NormalStrategy s) (I : FMSInstance s) : Prop :=
  (∀ x y a b, conditionalFmsRule x.val y.val a.val b.val=false →
    S.probability (I.qA x) (I.qB y) (I.aA a) (I.aB b)=0) ∧
  (∀ x, ∑ a, S.measurements.alice (I.qA x) (I.aA a)=1) ∧
  (∀ y, ∑ b, S.measurements.bob (I.qB y) (I.aB b)=1)

def flagA {s} (S : NormalStrategy s) (I : FMSInstance s) : Op :=
  S.measurements.alice (I.qA 0) (I.aA 0)
def magicA {s} (S : NormalStrategy s) (I : FMSInstance s) (i : Fin 4) : Op :=
  if i=0 then S.measurements.alice (I.qA 4) (I.aA 2)
  else S.measurements.alice (I.qA 3) (I.aA ⟨i.val+1,by omega⟩)
def transportA {s} (S : NormalStrategy s) (I : FMSInstance s) : Op :=
  magicA S I 0 * (S.measurements.alice (I.qA 3) (I.aA 0)-
    S.measurements.alice (I.qA 3) (I.aA 1))*flagA S I


def transportB {s} (S : NormalStrategy s) (I : FMSInstance s) : Op :=
  (Real.sqrt 2:ℂ) •
    (S.measurements.bob (I.qB 0) (I.aB 1)*
     S.measurements.bob (I.qB 4) (I.aB 2)*
     (S.measurements.bob (I.qB 3) (I.aB 0)-S.measurements.bob (I.qB 3) (I.aB 1))*
     S.measurements.bob (I.qB 0) (I.aB 0))


theorem shared_sign_unique (X X' Y T P : Op)
    (hT : DenseRange T) (hX : X*T=T*Y) (hX' : X'*T=T*Y)
    (hjoint : X'*P=P*X') : X'=X ∧ X*P=P*X := by
  have hz : (X'-X)*T=0 := by rw [sub_mul,hX',hX,sub_self]
  have heq : X'=X := sub_eq_zero.mp (Preliminaries.dense_range_cancel _ _ hT hz)
  exact ⟨heq,by simpa [heq] using hjoint⟩

theorem calibrated_sign_anticommute (X Y Δ T : Op) (hT : DenseRange T)
    (h00 : X*T=T*Y) (h11 : X*Δ*T= -(Δ*T*Y)) : X*Δ= -(Δ*X) := by
  have hz : (X*Δ+Δ*X)*T=0 := by
    calc
      _ = X*Δ*T+Δ*(X*T) := by noncomm_ring
      _ = -(Δ*T*Y)+Δ*(T*Y) := by rw [h11,h00]
      _ = 0 := by rw [mul_assoc]; exact neg_add_cancel _
  exact eq_neg_of_add_eq_zero_left (Preliminaries.dense_range_cancel _ _ hT hz)

theorem calibrated_density_commutes (X Y T : Op) (hX : star X=X) (hY : star Y=Y)
    (hXT : X*T=T*Y) : X*(T*star T)=(T*star T)*X := by
  have hstar : star T*X=Y*star T := by
    have h := congrArg (fun L : Op => star L) hXT
    simpa only [star_mul,hX,hY] using h
  calc
    X*(T*star T)=(X*T)*star T := by rw [mul_assoc]
    _=(T*Y)*star T := by rw [hXT]
    _=T*(Y*star T) := by rw [mul_assoc]
    _=T*(star T*X) := by rw [← hstar]
    _=(T*star T)*X := by rw [mul_assoc]

/-- Lemma 4.2, joint-refinement interface. Unchanged opposite questions give
the same dense intertwining block; sharp old coarse effects force commutation.
The conclusion includes the simultaneous honest refinement in the reverse direction. -/
theorem joint_refinement_iff {n : ℕ} (E : Fin n → Op)
    (hE : ∀ a,Projection (E a)) (hs : ∑ a,E a=1) (P : Op) (hP : Projection P)
    (T : Op) (hT : DenseRange T) :
    (∃ Q : Fin n → Fin 2 → Op,
      (∀ a z,Positive (Q a z)) ∧ (∑ a,∑ z,Q a z)=1 ∧
      (∀ a,(∑ z,Q a z)*T=E a*T) ∧ (∑ a,Q a 1)=P) ↔
    ∀ a,E a*P=P*E a := by
  constructor
  · rintro ⟨Q,hQ,hqs,hrows,hcol⟩
    have hrow a : (∑ z,Q a z)=E a := by
      apply sub_eq_zero.mp
      apply Preliminaries.dense_range_cancel _ T hT
      rw [sub_mul,hrows,sub_self]
    have hcol0 : (∑ a,Q a 0)=1-P := by
      have h := hqs
      simp only [Fin.sum_univ_two] at h
      rw [Finset.sum_add_distrib,hcol] at h
      exact eq_sub_of_add_eq h
    have hcols z : Projection (∑ a,Q a z) := by
      by_cases hz : z=1
      · subst z; rw [hcol]; exact hP
      · have hz0 : z=0 := by omega
        subst z; rw [hcol0]; exact projection_compl P hP
    have hj := Preliminaries.sharp_joint Q hQ hqs (fun a => (hrow a).symm ▸ hE a) hcols
    intro a
    have hx : Q a 1=E a*P := by simpa only [hrow,hcol] using hj a 1
    have hself : star (Q a 1)=Q a 1 := (hQ a 1).isSelfAdjoint
    calc
      E a*P = Q a 1 := hx.symm
      _ = star (Q a 1) := hself.symm
      _ = P*E a := by rw [hx,star_mul,hP.1,(hE a).1]
  · intro hc
    let Q : Fin n → Fin 2 → Op := fun a z => E a*(if z=1 then P else 1-P)
    have hrow a : (∑ z,Q a z)=E a := by
      simp only [Fin.sum_univ_two,Q,show (0:Fin 2)≠1 by decide,ite_false,ite_true]
      rw [mul_sub,mul_one]; abel
    refine ⟨Q,?_,?_,?_,?_⟩
    · intro a z
      apply ContinuousLinearMap.IsPositive.of_isStarProjection
      have hz : Projection (Q a z) := by
        dsimp [Q]
        split_ifs
        · exact projection_product _ _ (hE a) hP (hc a)
        · apply projection_product _ _ (hE a) (projection_compl P hP)
          rw [mul_sub,sub_mul,mul_one,one_mul,hc]
      exact ⟨hz.2,hz.1⟩
    · simp_rw [hrow]; exact hs
    · intro a; rw [hrow]
    · simp only [Q,ite_true,← Finset.sum_mul,hs,one_mul]

structure LabelRefinementInstance (s : Scenario) (I : FMSInstance s) where
  newA : QA s
  newB : QB s
  answerA : Fin 6 → Fin 2 → AA s
  answerB : Fin 6 → Fin 2 → BB s
  injectiveA : Function.Injective (fun az : Fin 6 × Fin 2 => answerA az.1 az.2)
  injectiveB : Function.Injective (fun az : Fin 6 × Fin 2 => answerB az.1 az.2)
  labelQA : QA s
  labelQB : QB s
  labelA : AA s
  labelB : BB s

def RefinementPerfect {s} (S : NormalStrategy s) (I : FMSInstance s)
    (F : LabelRefinementInstance s I) : Prop :=
  ConditionalPerfect S I ∧
  (∑ a,∑ z,S.measurements.alice F.newA (F.answerA a z))=1 ∧
  (∑ b,∑ z,S.measurements.bob F.newB (F.answerB b z))=1 ∧
  (∀ y : Fin 5,y.val ∈ [0,3,4] → ∀ a z b,
    conditionalFmsRule 3 y.val a.val b.val=false →
      S.probability F.newA (I.qB y) (F.answerA a z) (I.aB b)=0) ∧
  (∀ x : Fin 5,x.val ∈ [0,3,4] → ∀ a b z,
    conditionalFmsRule x.val 3 a.val b.val=false →
      S.probability (I.qA x) F.newB (I.aA a) (F.answerB b z)=0) ∧
  (∀ a z b,¬ (z.val=1 ↔ b=F.labelB) →
    S.probability F.newA F.labelQB (F.answerA a z) b=0) ∧
  (∀ a b z,¬ (z.val=1 ↔ a=F.labelA) →
    S.probability F.labelQA F.newB a (F.answerB b z)=0) ∧
  (∀ k,0<S.weight k →
    S.measurements.left F.labelQA F.labelA (S.vector k)=
      S.measurements.right F.labelQB F.labelB (S.vector k))

/-- Eq. (8), rational 3-4-5 graph certificate; u is the actual off-diagonal block. -/
theorem graph_certificate (Fi Fj G H Gc Hc : Op)
    (hFi : Projection Fi) (hFj : Projection Fj) (horth : Fi*Fj=0)
    (hG : Projection G) (hH : Projection H) (hGc : Projection Gc) (hHc : Projection Hc)
    (sG : G+Gc=Fi+Fj) (sH : H+Hc=Fi+Fj)
    (hrow : (5:ℂ) • H+Fi+Fj=(3:ℂ) • Fi+(4:ℂ) • G) :
    let u := Fi*((2:ℂ) • G-(Fi+Fj))*Fj
    star u*u=Fj ∧ u*star u=Fi := by
  exact ProjectionGraph.graph_certificate Fi Fj G H Gc Hc hFi hFj horth hG hH hGc hHc sG sH hrow

/-- Eq. (9), triangle projectivity certifies actual multiplication. -/
theorem triangle_product (u v w : Op)
    (hu : Unitary u) (hv : Unitary v) (hw : Unitary w)
    (htri : let P : Matrix (Fin 3) (Fin 3) Op :=
      !![(1/3:ℂ) • (1:Op), (1/3:ℂ) • u, (1/3:ℂ) • w;
         (1/3:ℂ) • star u, (1/3:ℂ) • (1:Op), (1/3:ℂ) • v;
         (1/3:ℂ) • star w, (1/3:ℂ) • star v, (1/3:ℂ) • (1:Op)]
      P*P=P) : w=u*v := by
  exact CompilerAlgebra.triangle_product u v w hu hv hw htri

/-- Eq. (10), the graph row has exactly the polynomial and its adjoint off diagonal. -/
theorem graph_linear_row {n} (q : Fin n → ℚ) (U : Fin n → Op)
    (hU : ∀ i, Unitary (U i)) :
    (∑ i, (q i:ℂ) • U i)=0 ↔
      (∑ i, (q i:ℂ) • (!![(0:Op),U i;star (U i),0] : Matrix (Fin 2) (Fin 2) Op))=0 := by
  exact CompilerAlgebra.graph_linear_row q U hU

/-- A certified row compiler, including preservation of arbitrary old questions. -/
structure ScenarioEmbedding (s t : Scenario) where
  qA : QA s → QA t
  qB : QB s → QB t
  aA : AA s → AA t
  aB : BB s → BB t
  iqA : Function.Injective qA
  iqB : Function.Injective qB
  iaA : Function.Injective aA
  iaB : Function.Injective aB

def Extends {s t} (E : ScenarioEmbedding s t) (S : NormalStrategy s) (T : NormalStrategy t) : Prop :=
  ∀ x y a b, S.probability x y a b = T.probability (E.qA x) (E.qB y) (E.aA a) (E.aB b)

structure NamedEvent (s : Scenario) where
  x : QA s
  y : QB s
  a : AA s
  b : BB s

structure Rows (s : Scenario) where
  count : ℕ
  event : Fin count → NamedEvent s
  rowCount : ℕ
  constant : Fin rowCount → ℚ
  coefficient : Fin rowCount → Fin count → ℚ

def RowsHold {s} (R : Rows s) (S : NormalStrategy s) : Prop :=
  ∃ hA hB : Density, MarginalA S hA ∧ MarginalB S hB ∧
    (∀ i k, 0 < S.weight k →
      S.measurements.left (R.event i).x (R.event i).a (S.vector k)=
      S.measurements.right (R.event i).y (R.event i).b (S.vector k)) ∧
    (∀ r, ((R.constant r:ℂ) • (1:Op)+∑ i, (R.coefficient r i:ℂ) •
      S.measurements.alice (R.event i).x (R.event i).a)*hA.op=0) ∧
    (∀ r, ((R.constant r:ℂ) • (1:Op)+∑ i, (R.coefficient r i:ℂ) •
      S.measurements.bob (R.event i).y (R.event i).b)*hB.op=0)

/-- The two binary coarse outcomes (the named answer and its complement)
are matched with zero disagreement probability on the original normal state. -/
def BinaryEventSynchronized {s} (S : NormalStrategy s) (e : NamedEvent s) : Prop :=
  ∀ a b, ¬ (a=e.a ↔ b=e.b) → S.probability e.x e.y a b=0

/-- A binary effect restricted to a reducing state support is a projection.
Its other binary outcome is the complementary projection in that support. -/
def BinaryProjectionOn (P A : Op) : Prop :=
  A*P=P*A ∧ Projection (P*A*P)

/-- The synchronized binary projections named by the finite row specification.
No condition is imposed on the other old questions or on label-label commutation. -/
def NamedBinaryProjections {s} (R : Rows s) (S : NormalStrategy s) : Prop :=
  ∃ (hA hB : Density) (eA eB : Op),
    MarginalA S hA ∧ MarginalB S hB ∧
    Preliminaries.SupportOf hA eA ∧ Preliminaries.SupportOf hB eB ∧
    (∀ i, BinaryProjectionOn eA (S.measurements.alice (R.event i).x (R.event i).a) ∧
      BinaryProjectionOn eB (S.measurements.bob (R.event i).y (R.event i).b)) ∧
    (∀ i, BinaryEventSynchronized S (R.event i))

theorem row_column_overlap {d : ℕ} (hd : 0<d) (V : Fin d → Op)
    (hV : ∀ j, Unitary (V j)) :
    let C : Matrix (Fin d) (Fin d) Op := fun i j => (1/(d:ℂ)) • (V i*star (V j))
    let R : Matrix (Fin d) (Fin d) Op := fun _ _ => (1/(d:ℂ)) • (1:Op)
    C*R=0 ↔ (∑ j, V j)=0 := by
  exact CompilerAlgebra.row_column_overlap hd V hV

/-- Eq. (13), exact row-zero probability, including the scalar density factor. -/
theorem row_loss_formula (L d : ℕ) (hd : 0<d) (S : Op) (hS : star S=S)
    (h : Density) (hs : Centralizes h.op S)
    (V : Fin d → Op) (hV : ∀ j, Unitary (V j))
    (hslots : ∑ j, V j=(2*(L:ℂ)) • S) :
    (1/(d:ℝ)^3) * (trace (h.op*(star (∑ j,V j)*(∑ j,V j)))).re =
      4*(L:ℝ)^2/(d:ℝ)^3 * (trace (h.op*(S*S))).re := by
  exact CompilerAlgebra.row_loss_formula L d hd S hS h hs V hV hslots

/-- Centralizer contraction encoding on faithful normal supports. The finite
eigenspaces are essential: this is not asserted for arbitrary contractions on a
zero-density infinite-dimensional summand. -/
theorem contraction_encoding (h : Density) (hf : Faithful h) (T : Op)
    (hT : Contraction T) (hc : Centralizes h.op T) :
    ∃ U V : Op,Unitary U ∧ Unitary V ∧ Centralizes h.op U ∧ Centralizes h.op V ∧
      T=(1/2:ℂ) • (U+V) := by
  exact DensityContraction.mean h hf T hT hc

/-- Exact structural assumptions for approximate compilation; no application
equation, diagonal isometry equation, or range-sum equation is assumed. -/
structure StructuralRealization (P : Presentation) where
  support : Op
  support_projection : Projection support
  density : Density
  density_supported : support*density.op=density.op
  faithful_on : ∀ v,support v=v → density.op v=0 → v=0
  label : ℕ → Op
  creation : Fin 4 → Op
  label_supported : ∀ i,support*label i=label i ∧ label i*support=label i
  creation_supported : ∀ a,support*creation a=creation a ∧ creation a*support=creation a
  typed : ∀ i : Fin P.types.length,TypedAt support (label i.val) P.types[i.val]
  creation_contractive : ∀ a,Contraction (creation a)
  centralizer : ∀ i,Centralizes density.op (label i)
  modular : ∀ a,density.op*creation a=(1/16:ℂ) • (creation a*density.op)

def applicationResiduals (P : Presentation) (R : StructuralRealization P) : List Op :=
  (List.ofFn (fun a : Fin 4 => a)).flatMap (fun a => List.ofFn (fun b : Fin 4 =>
    star (R.creation a)*R.creation b-(if a=b then R.support else 0))) ++
  [((∑ a,R.creation a*star (R.creation a))-(R.support-R.label P.root))] ++
  P.central.map (fun p => p.eval R.support R.label) ++
  P.endpoints.map (fun r => r.1.eval R.support R.label*R.creation r.2.1-
    R.creation r.2.2.1*r.2.2.2.eval R.support R.label) ++
  P.zeros.map (fun r => r.1.eval R.support R.label*R.creation r.2) ++
  P.linear.map (fun row => (row.map (fun r =>
    r.1.eval R.support R.label*R.creation r.2.1*r.2.2.eval R.support R.label)).sum)

/-- The full four-bridge contract. Every own prerequisite is a blueprint theorem,
never a field supplied by the final theorem's caller. -/
def Compiled (P : Presentation) (c : ℕ) : Prop :=
  ∃ G, decodeGame c=some G ∧
    (HasPerfect G ↔ Nonempty (NormalRealization P)) ∧
    (HasFiniteEntropyPerfect G ↔ ∃ R : NormalRealization P, RealizationFiniteEntropy R) ∧
    (HasFinitePerfect G → ∃ R : NormalRealization P, FiniteRealization R) ∧
    (∃ (x : QA G.scenario) (a : AA G.scenario),∀ S,Perfect G S →
      ∃ (R : NormalRealization P) (h : Density) (e : Op),
        MarginalA S h ∧ Preliminaries.SupportOf h e ∧
        R.support=e*S.measurements.alice x a*e ∧
        R.density.op=(121:ℂ) • (R.support*h.op*R.support) ∧
        (trace (h.op*R.support)).re=1/121)

theorem scaffold_mass (m : Fin 5 → ℝ) (h : ∀ g : Fin 4, m ⟨g.val+1,by omega⟩=2*m ⟨g.val,by omega⟩)
    (hs : m 0+4*(m 1+m 2+m 3+m 4)=1) : m 0=1/121 := by
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  norm_num at h0 h1 h2 h3
  linarith

/-- Eq. (18), the very same four calibrated bridges transport every label;
no commutation of labels and no new independently gauged bridge is assumed. -/
theorem same_bridge_transport {n : ℕ} (L : Fin 5 → Fin n → Op)
    (w1 w2 w3 w4 : Op)
    (h1 : ∀ k,L 1 k*w1=w1*L 0 k) (h2 : ∀ k,L 2 k*w2=w2*L 1 k)
    (h3 : ∀ k,L 3 k*w3=w3*L 2 k) (h4 : ∀ k,L 4 k*w4=w4*L 3 k) :
    ∀ k,L 4 k*(w4*w3*w2*w1)=(w4*w3*w2*w1)*L 0 k := by
  intro k
  calc
    L 4 k*(w4*w3*w2*w1)=(L 4 k*w4)*w3*w2*w1 := by noncomm_ring
    _=(w4*L 3 k)*w3*w2*w1 := by rw [h4]
    _=w4*(L 3 k*w3)*w2*w1 := by noncomm_ring
    _=w4*(w3*L 2 k)*w2*w1 := by rw [h3]
    _=(w4*w3)*(L 2 k*w2)*w1 := by noncomm_ring
    _=(w4*w3)*(w2*L 1 k)*w1 := by rw [h2]
    _=(w4*w3*w2)*(L 1 k*w1) := by noncomm_ring
    _=(w4*w3*w2)*(w1*L 0 k) := by rw [h1]
    _=(w4*w3*w2*w1)*L 0 k := by noncomm_ring

end Sigma2.Compiler
