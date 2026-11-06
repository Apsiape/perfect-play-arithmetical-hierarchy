import Sigma2.ReductionPresentationBase
import Sigma2.CompilerScaffold

set_option maxHeartbeats 200000

noncomputable section
namespace Sigma2

/-- Printed Definition 4.4: "Every label used on a left endpoint is included
in the transported unitary list" and "the root projection is transported even
when it occurs in no endpoint equation".  The left expression in every finite
sum term is a left endpoint too.  These are exactly the two conjuncts missing
from the frozen `Presentation.admissible`; this wrapper changes no old syntax. -/
def PaperAdmissible (P : Presentation) : Prop :=
  P.admissible ∧ P.root ∈ P.transported ∧
    ∀ row ∈ P.linear, ∀ r ∈ row, ∀ i ∈ r.1.labels, i ∈ P.transported

namespace PaperAdmissibility

/-- Effective finite saturation; every declared label is transported. -/
def saturate (P : Presentation) : Presentation :=
  { P with transported := List.range P.types.length }

theorem buildPresentation_paper_admissible (M : Tree.Automaton) :
    PaperAdmissible (Reduction.buildPresentation M) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      change i ∈ List.range 10 at hi
      have hb := List.mem_range.mp hi
      change i < (Reduction.buildPresentation M).types.length
      simp only [Reduction.buildPresentation, List.length_append,
        List.length_cons, List.length_nil, List.length_replicate]
      omega
    all_goals simp [Reduction.buildPresentation]
  · change 0 ∈ List.range 10
    simp
  · simp [Reduction.buildPresentation]

theorem application_paper_admissible (M : Tree.Automaton) :
    PaperAdmissible (Reduction.applicationPresentation M) := by
  refine ⟨Reduction.application_admissible M, ?_, ?_⟩
  · change 0 ∈ List.range 10
    simp
  · simp [Reduction.applicationPresentation, Reduction.buildPresentation]

theorem input_paper_admissible (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) :
    PaperAdmissible (Reduction.inputPresentation R hR e) :=
  application_paper_admissible _

theorem saturation_paper_admissible (P : Presentation) (hP : P.admissible) :
    PaperAdmissible (saturate P) := by
  rcases hP with ⟨hroot, htransport, hcentral, hendpoints, hzeros, hlinear⟩
  refine ⟨⟨hroot, ?_, hcentral, ?_, ?_, hlinear⟩, ?_, ?_⟩
  · intro i hi
    exact List.mem_range.mp hi
  · intro r hr
    exact ⟨fun i hi => List.mem_range.mpr (htransport i ((hendpoints r hr).1 i hi)),
      (hendpoints r hr).2⟩
  · intro r hr i hi
    exact List.mem_range.mpr (htransport i (hzeros r hr i hi))
  · exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp hroot).1
  · intro row hr r hrr i hi
    exact List.mem_range.mpr ((hlinear row hr r hrr).1 i hi)

/- The indexed record TYPES are not definitionally equal: their Presentation
parameter differs.  The following maps copy every field; all the individual
operator, density, type and equation fields are definitionally unchanged. -/

def normalToSaturated {P : Presentation} (R : NormalRealization (P)) :
    NormalRealization (saturate P) where
  support := R.support
  support_projection := R.support_projection
  density := R.density
  density_supported := R.density_supported
  faithful_on := R.faithful_on
  label := R.label
  creation := R.creation
  label_supported := R.label_supported
  creation_supported := R.creation_supported
  typed := R.typed
  centralizer := R.centralizer
  isometries := R.isometries
  ranges := R.ranges
  modular := R.modular
  central_equations := R.central_equations
  endpoint_equations := R.endpoint_equations
  zero_equations := R.zero_equations
  linear_equations := R.linear_equations

def normalFromSaturated {P : Presentation} (R : NormalRealization (saturate P)) :
    NormalRealization (P) where
  support := R.support
  support_projection := R.support_projection
  density := R.density
  density_supported := R.density_supported
  faithful_on := R.faithful_on
  label := R.label
  creation := R.creation
  label_supported := R.label_supported
  creation_supported := R.creation_supported
  typed := R.typed
  centralizer := R.centralizer
  isometries := R.isometries
  ranges := R.ranges
  modular := R.modular
  central_equations := R.central_equations
  endpoint_equations := R.endpoint_equations
  zero_equations := R.zero_equations
  linear_equations := R.linear_equations

def structuralToSaturated {P : Presentation} (R : Compiler.StructuralRealization (P)) :
    Compiler.StructuralRealization (saturate P) where
  support := R.support
  support_projection := R.support_projection
  density := R.density
  density_supported := R.density_supported
  faithful_on := R.faithful_on
  label := R.label
  creation := R.creation
  label_supported := R.label_supported
  creation_supported := R.creation_supported
  typed := R.typed
  creation_contractive := R.creation_contractive
  centralizer := R.centralizer
  modular := R.modular

def structuralFromSaturated {P : Presentation} (R : Compiler.StructuralRealization (saturate P)) :
    Compiler.StructuralRealization (P) where
  support := R.support
  support_projection := R.support_projection
  density := R.density
  density_supported := R.density_supported
  faithful_on := R.faithful_on
  label := R.label
  creation := R.creation
  label_supported := R.label_supported
  creation_supported := R.creation_supported
  typed := R.typed
  creation_contractive := R.creation_contractive
  centralizer := R.centralizer
  modular := R.modular

/-- Same realizations via field-preserving inverse maps; the inverse laws
require record extensionality (cases) and proof irrelevance, rather than rfl
between the two indexed record types. -/
def normalEquiv (P : Presentation) : NormalRealization P ≃ NormalRealization (saturate P) where
  toFun := normalToSaturated
  invFun := normalFromSaturated
  left_inv := by intro R; cases R; rfl
  right_inv := by intro R; cases R; rfl

def structuralEquiv (P : Presentation) :
    Compiler.StructuralRealization P ≃ Compiler.StructuralRealization (saturate P) where
  toFun := structuralToSaturated
  invFun := structuralFromSaturated
  left_inv := by intro R; cases R; rfl
  right_inv := by intro R; cases R; rfl

/-- Residual equality after the field-preserving map is definitional. -/
theorem saturation_residuals (P : Presentation) (R : Compiler.StructuralRealization P) :
    Compiler.applicationResiduals (saturate P) (structuralToSaturated R) =
      Compiler.applicationResiduals P R := rfl

/- The recursive `expression P` retains the whole P as a parameter.
Consequently game equality is propositional: prove the recursion invariant
before rewriting the finite compiler tables.  No compiler table is changed. -/
open CompilerScaffold

theorem saturation_encodingCount (P : Presentation) :
    encodingCount (saturate P) = encodingCount P := rfl

theorem saturation_encodingOffset (P : Presentation) (i : ℕ) :
    encodingOffset (saturate P) i = encodingOffset P i := rfl

theorem saturation_copyAtom (P : Presentation) (r i : ℕ) :
    copyAtom (saturate P) r i = copyAtom P r i := rfl

theorem saturation_creation (P : Presentation) (a : ℕ) :
    creation (saturate P) a = creation P a := rfl

theorem saturation_labelCopy (P : Presentation) (r i : ℕ) :
    labelCopy (saturate P) r i = labelCopy P r i := rfl

theorem saturation_expression (P : Presentation) (r : ℕ) (p : Expr) :
    expression (saturate P) r p = expression P r p := by
  induction p with
  | scalar q => rfl
  | label i => exact saturation_labelCopy P r i
  | add p q hp hq => simp only [expression, hp, hq]
  | mul p q hp hq => simp only [expression, hp, hq]
  | adj p hp => simp only [expression, hp]

theorem saturation_blockAtom (P : Presentation) (g l : ℕ) :
    blockAtom (saturate P) g l = blockAtom P g l := rfl

theorem saturation_transportTerm (P : Presentation) (g l : ℕ) :
    transportTerm (saturate P) g l = transportTerm P g l := by
  funext k
  rfl

theorem saturation_expression_fun (P : Presentation) (r : ℕ) :
    expression (saturate P) r = expression P r :=
  funext (saturation_expression P r)

theorem saturation_structuralPolynomials (P : Presentation) :
    structuralPolynomials (saturate P) = structuralPolynomials P := by
  simp only [structuralPolynomials, saturation_encodingCount, saturation_copyAtom,
    saturation_blockAtom, saturation_creation, saturation_encodingOffset,
    saturation_transportTerm]
  rfl

theorem saturation_applicationPolynomials (P : Presentation) :
    applicationPolynomials (saturate P) = applicationPolynomials P := by
  simp only [applicationPolynomials, saturation_creation, saturation_labelCopy,
    saturation_expression_fun, saturation_expression]
  rfl

theorem saturation_polynomials (P : Presentation) :
    polynomials (saturate P) = polynomials P := by
  simp only [polynomials, saturation_structuralPolynomials,
    saturation_applicationPolynomials]

theorem saturation_words (P : Presentation) : words (saturate P) = words P := by
  simp only [words, saturation_polynomials]

theorem saturation_rowList (P : Presentation) : rowList (saturate P) = rowList P := by
  simp only [rowList, saturation_words, saturation_polynomials]

theorem saturation_names (P : Presentation) : names (saturate P) = names P := by
  simp only [names, saturation_encodingCount, saturation_rowList]

theorem saturation_refinementCount (P : Presentation) :
    refinementCount (saturate P) = refinementCount P := rfl

theorem saturation_refinementLabel (P : Presentation) (g k : ℕ) :
    refinementLabel (saturate P) g k = refinementLabel P g k := rfl

/- The dependent game/Rows assembly can be factored through its encoding
count, name list and row list. These helper definitions copy only the frozen
assembly formulas; the factorization is definitional, not a new compiler. -/
namespace TableData
open CompilerScaffold Compiler

def tableRefinementLabel (c : ℕ) (g k : ℕ) : ProjectionName :=
  if k<3 then .frame k else if k<6 then .graph [] (k-3) 0
  else .graph [(33+5*c+g*c+(k-6),false)] 0 0

def tableScenario (c : ℕ) (ns : List ProjectionName) : Scenario where
  questionsA := ns.length+20+4*(6+c)
  questionsB := ns.length+20+4*(6+c)
  answersA := 11
  answersB := 11

def tableQuestion (c : ℕ) (ns : List ProjectionName) (x : ℕ) : Question :=
  let n := ns.length
  if x<n then .binary (ns[x]?.getD (.frame 0))
  else if x<n+20 then .fms ((x-n)/5) ((x-n)%5)
  else if x<n+20+4*(6+c) then
    .refinement ((x-n-20)/(6+c)) ((x-n-20)%(6+c))
  else .padding

def tableDirected (c : ℕ) (alice : Bool) (q p : Question) (a b : ℕ) : Bool :=
  match q,p with
  | .fms g x,.binary n => fmsBinding alice g x n a b
  | .refinement g k,.binary n =>
      if n=tableRefinementLabel c g k then decide ((a%2=1) ↔ b=1) else true
  | .refinement g _,.fms h y =>
      if g=h ∧ y ∈ [0,3,4] then
        if alice then conditionalFmsRule 3 y (a/2) b
        else conditionalFmsRule y 3 b (a/2)
      else true
  | _,_ => true

def tableRule (c : ℕ) (q p : Question) (a b : ℕ) : Bool :=
  valid q a && valid p b &&
  (match q,p with
    | .binary n,.binary m => if n=m then decide (a=b) else true
    | .fms g x,.fms h y => if g=h then conditionalFmsRule x y a b else true
    | _,_ => true) &&
  tableDirected c true q p a b && tableDirected c false p q b a

def tablePreGame (c : ℕ) (ns : List ProjectionName) : Game where
  scenario := tableScenario c ns
  distribution := fun _ _ => 1 / (((tableScenario c ns).questionsA+1 : ℕ) *
    ((tableScenario c ns).questionsB+1 : ℕ) : ℕ)
  distribution_nonneg := by intro x y; positivity
  distribution_sum := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    field_simp
  accepts := fun x y a b => tableRule c (tableQuestion c ns x.val) (tableQuestion c ns y.val) a.val b.val

def tableEvent (c : ℕ) (ns : List ProjectionName) (i : Fin ns.length) : NamedEvent (tableScenario c ns) where
  x := ⟨i.val,by have := i.isLt; dsimp [tableScenario]; omega⟩
  y := ⟨i.val,by have := i.isLt; dsimp [tableScenario]; omega⟩
  a := ⟨1,by change 1<12; decide⟩
  b := ⟨1,by change 1<12; decide⟩

def tableRows (c : ℕ) (ns : List ProjectionName) (rs : List RationalRow) : Rows (tableScenario c ns) where
  count := ns.length
  event := tableEvent c ns
  rowCount := rs.length
  constant := fun r => (rs[r.val]'r.isLt).constant
  coefficient := fun r i => coefficient (rs[r.val]'r.isLt) (ns[i.val]'i.isLt)

def tableGame (c : ℕ) (ns : List ProjectionName) (rs : List RationalRow) : Game :=
  RowGame.game (tablePreGame c ns) (tableRows c ns rs)

end TableData

attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.encodingCount RowGame.game RowGame.questions
  RowSlots.raw RowSlots.bound RowSlots.squares RowSlots.dimension

theorem finalGame_factor (P : Presentation) :
    finalGame P = TableData.tableGame (encodingCount P) (names P) (rowList P) := rfl

/-- Game equality needs the recursive-expression invariant above; it is not
claimed as a bare definitional equality between the two compiled games. -/
theorem saturation_finalGame (P : Presentation) :
    CompilerScaffold.finalGame (saturate P) = CompilerScaffold.finalGame P := by
  rw [finalGame_factor (saturate P), finalGame_factor P,
    saturation_encodingCount, saturation_names, saturation_rowList]

theorem saturation_codeFor (P : Presentation) :
    CompilerScaffold.codeFor (saturate P) = CompilerScaffold.codeFor P :=
  congrArg GameTable.code (saturation_finalGame P)

/-- Complete saturation bridge: admissibility needs a proof, realizations need
an equivalence of indexed records, residuals reduce by rfl, and game equality
requires the recursive-expression proof and table rewrites. -/
theorem saturation_bridge (P : Presentation) (hP : P.admissible) :
    PaperAdmissible (saturate P) ∧
      Nonempty (NormalRealization P ≃ NormalRealization (saturate P)) ∧
      (∀ R : Compiler.StructuralRealization P,
        Compiler.applicationResiduals (saturate P) (structuralToSaturated R) =
          Compiler.applicationResiduals P R) ∧
      CompilerScaffold.finalGame (saturate P) = CompilerScaffold.finalGame P :=
  ⟨saturation_paper_admissible P hP, ⟨normalEquiv P⟩,
    saturation_residuals P, saturation_finalGame P⟩

/-- Exact compiler contracts transfer back across saturation, including the
fixed source event, actual extracted density, finite entropy and finite support. -/
theorem compiled_of_saturated (P : Presentation) (c : ℕ)
    (h : Compiler.Compiled (saturate P) c) : Compiler.Compiled P c := by
  rcases h with ⟨G, hd, hn, he, hf, hs⟩
  refine ⟨G, hd, ?_, ?_, ?_, ?_⟩
  · exact ⟨fun hG => (hn.mp hG).map normalFromSaturated,
      fun hR => hn.mpr (hR.map normalToSaturated)⟩
  · constructor
    · intro hG
      obtain ⟨R, hR⟩ := he.mp hG
      exact ⟨normalFromSaturated R, hR⟩
    · rintro ⟨R, hR⟩
      exact he.mpr ⟨normalToSaturated R, hR⟩
  · intro hG
    obtain ⟨R, hR⟩ := hf hG
    exact ⟨normalFromSaturated R, hR⟩
  · obtain ⟨x, a, hs⟩ := hs
    refine ⟨x, a, ?_⟩
    intro S hS
    obtain ⟨R, h, e, hA, he, hsupport, hdensity, hmass⟩ := hs S hS
    exact ⟨normalFromSaturated R, h, e, hA, he, hsupport, hdensity, hmass⟩

theorem approxCompiled_of_saturated (P : Presentation) (c : ℕ)
    (h : Compiler.ApproxCompiled (saturate P) c) : Compiler.ApproxCompiled P c := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, ?_⟩
  intro G hd R
  exact h G hd (structuralToSaturated R)

end PaperAdmissibility
end Sigma2

#print axioms Sigma2.PaperAdmissibility.application_paper_admissible
#print axioms Sigma2.PaperAdmissibility.saturation_paper_admissible
#print axioms Sigma2.PaperAdmissibility.saturation_bridge
#print axioms Sigma2.PaperAdmissibility.compiled_of_saturated
#print axioms Sigma2.PaperAdmissibility.approxCompiled_of_saturated
