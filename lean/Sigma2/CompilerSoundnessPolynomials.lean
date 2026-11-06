import Sigma2.CompilerSoundnessWordEvaluation
import Sigma2.CompilerSoundnessCover

/-! Decode all original structural and application polynomials on the common frame. -/
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessPolynomials
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessFrame CompilerSoundnessGraphs CompilerSoundnessJoints
  CompilerSoundnessTriangles CompilerSoundnessExtraction CompilerSoundnessWords
  CompilerSoundnessWordClosure CompilerSoundnessWordEvaluation CompilerSoundnessCover Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

theorem closure_self (w : Word) : w ∈ wordClosure w := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨w.length,List.mem_range.mpr (by omega),by simp⟩

theorem polynomial_word_mem (P : Presentation) (p : Poly) (hp : p ∈ polynomials P)
    (t : ℚ × Word) (ht : t ∈ p) : t.2 ∈ words P := by
  simp only [words,List.mem_dedup]
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨p,hp,List.mem_flatMap.mpr ⟨t,ht,closure_self t.2⟩⟩

theorem parameter_word_mem (P : Presentation) (p : Fin 25) : [(p.val,false)] ∈ words P := by
  let q := sub (mul (atom p.val) (atom p.val)) one
  have hp : q ∈ polynomials P := by
    simp only [polynomials,List.mem_append]
    left
    simp only [structuralPolynomials,List.mem_append]
    left; left; left; left; left; right
    exact List.mem_map.mpr ⟨p.val,List.mem_range.mpr p.isLt,rfl⟩
  have ht : (1,[(p.val,false),(p.val,false)]) ∈ q := by
    simp [q,CompilerScaffold.sub,CompilerScaffold.mul,atom]
  have hw := polynomial_word_mem P q hp _ ht
  simpa using words_take P [(p.val,false),(p.val,false)] hw 1

theorem parameter_reflection (E : SupportedScaffold P) (p : Fin 25) :
    unitaries E p.val*projectionA P E.strategy E.supportA (.frame 0)=
      (2:ℂ) • (projectionA P E.strategy E.supportA (.parameter p.val)*
        projectionA P E.strategy E.supportA (.frame 0))-
      projectionA P E.strategy E.supportA (.frame 0) := by
  let F := projectionA P E.strategy E.supportA
  let q := graphBlock F [] 0
  have hq : q*star q=F (.frame 0) := (E.graph [] (empty_mem_words P) 0).2
  have hp := (parameter_graph P E.supportA F E.sharpA E.frame.2.1 E.rowsA p 0).2.1
  simp only [Fin.val_zero] at hp
  rw [positive_on_frame E p.val (parameter_word_mem P p)]
  change graphBlock F [(p.val,false)] 0*star q=_
  rw [hp]
  calc
    _=(2:ℂ) • (F (.parameter p.val)*(q*star q))-q*star q := by
      simp only [sub_mul,smul_mul_assoc,mul_assoc]
      rfl
    _=_ := by rw [hq]

theorem graphPolynomial_return (E : SupportedScaffold P) (p : Poly) :
    let F := projectionA P E.strategy E.supportA
    graphPolynomial F p*star (graphBlock F [] 0)=
      (p.map (fun t => (t.1:ℂ) • wordCorner E t.2)).sum := by
  induction p with
  | nil => simp [graphPolynomial]
  | cons t p ih =>
    simp only [graphPolynomial,List.map_cons,List.sum_cons,add_mul,smul_mul_assoc] at ih ⊢
    rw [ih]
    rfl

theorem corner_poly_evaluation (E : SupportedScaffold P) (p : Poly)
    (hp : ∀ t ∈ p,t.2 ∈ words P) :
    evalPoly (unitaries E) p*projectionA P E.strategy E.supportA (.frame 0)=
      (p.map (fun t => (t.1:ℂ) • wordCorner E t.2)).sum := by
  induction p with
  | nil => simp [evalPoly]
  | cons t p ih =>
    simp only [evalPoly] at ih
    simp only [evalPoly,List.map_cons,List.sum_cons,add_mul,smul_mul_assoc]
    rw [evalWord_retained E t.2 (hp t (by simp)),ih (fun s hs => hp s (by simp [hs]))]

/-- Both structural and application equations are derived from the actual row list. -/
theorem polynomial_equations (E : SupportedScaffold P) (p : Poly) (hp : p ∈ polynomials P) :
    evalPoly (unitaries E) p*projectionA P E.strategy E.supportA (.frame 0)=0 := by
  let F := projectionA P E.strategy E.supportA
  have hrow := E.rowsA (polynomialRow p) (polynomialRow_mem P p hp)
  have hg : graphPolynomial F p=0 := by
    have hh := congrArg (fun X : Op => F (.frame 0)*X*F (.frame 1)) hrow
    rw [polynomial_row_compression,mul_zero,zero_mul] at hh
    exact hh
  rw [corner_poly_evaluation E p (fun t ht => polynomial_word_mem P p hp t ht),
    ← graphPolynomial_return E p,hg,zero_mul]

theorem structural_equations (E : SupportedScaffold P) (p : Poly) (hp : p ∈ structuralPolynomials P) :
    evalPoly (unitaries E) p*projectionA P E.strategy E.supportA (.frame 0)=0 :=
  polynomial_equations E p (by simp only [polynomials,List.mem_append]; exact Or.inl hp)

theorem application_equations (E : SupportedScaffold P) (p : Poly) (hp : p ∈ applicationPolynomials P) :
    evalPoly (unitaries E) p*projectionA P E.strategy E.supportA (.frame 0)=0 :=
  polynomial_equations E p (by simp only [polynomials,List.mem_append]; exact Or.inr hp)

theorem density_star (h : Density) (A : Op) (hc : Centralizes h.op A) : Centralizes h.op (star A) := by
  have hs : star h.op=h.op := h.positive.isSelfAdjoint
  change h.op*star A=star A*h.op
  simpa only [star_mul,hs] using (congrArg (fun X : Op => star X) hc).symm

theorem graphBlock_central (E : SupportedScaffold P) (w : Word) (k : ℕ) :
    Centralizes E.densityA.op (graphBlock (projectionA P E.strategy E.supportA) w k) := by
  let F := projectionA P E.strategy E.supportA
  have hc (n : ProjectionName) : Commute E.densityA.op (F n) :=
    CompilerSoundnessNames.centralA P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws n
  let ij := pairs[k]?.getD (0,1)
  exact ((hc (.frame ij.1)).mul_right (((hc (.graph w k 0)).smul_right (2:ℂ)).sub_right
    ((hc (.frame ij.1)).add_right (hc (.frame ij.2))))).mul_right (hc (.frame ij.2))

theorem wordCorner_central (E : SupportedScaffold P) (w : Word) :
    Centralizes E.densityA.op (wordCorner E w) :=
  (show Commute E.densityA.op (graphBlock (projectionA P E.strategy E.supportA) w 0) from graphBlock_central E w 0).mul_right (density_star E.densityA _ (graphBlock_central E [] 0))

theorem unitaries_central (E : SupportedScaffold P) (i : ℕ) : Centralizes E.densityA.op (unitaries E i) := by
  unfold unitaries
  split_ifs
  · exact (show Commute E.densityA.op (wordCorner E [(i,false)]) from wordCorner_central E _).add_right ((Commute.one_right _).sub_right
      (CompilerSoundnessNames.centralA P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws _))
  · exact Commute.one_right _

theorem evalWord_central (E : SupportedScaffold P) (w : Word) : Centralizes E.densityA.op (evalWord (unitaries E) w) := by
  induction w with
  | nil => exact Commute.one_right _
  | cons t w ih =>
    change Centralizes E.densityA.op ((if t.2 then star (unitaries E t.1) else unitaries E t.1)*_)
    apply Commute.mul_right _ ih
    cases t with
    | mk i b =>
      cases b
      · exact unitaries_central E i
      · exact density_star E.densityA _ (unitaries_central E i)

#print axioms parameter_reflection
#print axioms polynomial_equations
#print axioms structural_equations
#print axioms application_equations
#print axioms unitaries_central
end Sigma2.CompilerSoundnessPolynomials
