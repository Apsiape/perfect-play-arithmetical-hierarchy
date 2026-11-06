import Sigma2.CompilerSoundnessBlockEquations

/-! Extend the one actual qutrit-frame corner through its original empty-word gauge. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessLift
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessBlockEquations CompilerSoundnessWords
  CompilerSoundnessGraphs CompilerSoundnessTriangles CompilerSoundnessJoints
  CompilerSoundnessPolynomials CompilerSoundnessWordEvaluation CompilerSoundnessCover
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def frames (E : SupportedScaffold P) (i : Fin 3) : Op :=
  projectionA P E.strategy E.supportA (.frame i.val)

def gauge (E : SupportedScaffold P) (i : Fin 3) : Op :=
  if i=0 then frame E else graphBlock (projectionA P E.strategy E.supportA) [] (i.val-1)

theorem gauge_block (E : SupportedScaffold P) (i : Fin 3) :
    FrameBlock (frames E) 0 i (gauge E i) := by
  fin_cases i
  · exact ⟨(E.sharpA _).2,(E.sharpA _).2⟩
  · simpa [gauge,frames,pairs,FrameBlock] using graph_frame_block
      (projectionA P E.strategy E.supportA) E.sharpA [] 0
  · simpa [gauge,frames,pairs,FrameBlock] using graph_frame_block
      (projectionA P E.strategy E.supportA) E.sharpA [] 1

theorem gauge_range (E : SupportedScaffold P) (i : Fin 3) :
    star (gauge E i)*gauge E i=frames E i ∧ gauge E i*star (gauge E i)=frame E := by
  fin_cases i
  · simpa [gauge,frames,(E.sharpA _).1] using And.intro (E.sharpA (.frame 0)).2 (E.sharpA (.frame 0)).2
  · simpa [gauge,frames,pairs] using E.graph [] (empty_mem_words P) 0
  · simpa [gauge,frames,pairs] using E.graph [] (empty_mem_words P) 1

theorem gauge_product (E : SupportedScaffold P) (i j : Fin 3) :
    gauge E i*star (gauge E j)=if i=j then frame E else 0 := by
  by_cases hij : i=j
  · subst j
    rw [if_pos rfl]
    exact (gauge_range E i).2
  · rw [if_neg hij]
    exact block_mul_zero (frames E) E.frame.2.1 0 i j 0 _ _ (gauge_block E i)
      (block_star (frames E) (fun k => E.sharpA _) 0 j _ (gauge_block E j)) hij

def spread (E : SupportedScaffold P) (X : Op) : Op :=
  ∑ i : Fin 3,star (gauge E i)*X*gauge E i

theorem spread_zero (E : SupportedScaffold P) : spread E 0=0 := by simp [spread]

theorem spread_add (E : SupportedScaffold P) (X Y : Op) :
    spread E (X+Y)=spread E X+spread E Y := by
  simp only [spread,mul_add,add_mul,Finset.sum_add_distrib]

theorem spread_sub (E : SupportedScaffold P) (X Y : Op) :
    spread E (X-Y)=spread E X-spread E Y := by
  simp only [spread,mul_sub,sub_mul,Finset.sum_sub_distrib]

theorem spread_smul (E : SupportedScaffold P) (c : ℂ) (X : Op) :
    spread E (c • X)=c • spread E X := by
  simp only [spread,mul_smul_comm,smul_mul_assoc,Finset.smul_sum]

theorem spread_star (E : SupportedScaffold P) (X : Op) : spread E (star X)=star (spread E X) := by
  rw [spread,spread,CompilerAlgebra.op_star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [star_mul,star_star,mul_assoc]

theorem spread_mul (E : SupportedScaffold P) (X Y : Op) (hX : X*frame E=X) :
    spread E (X*Y)=spread E X*spread E Y := by
  unfold spread
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum]
  symm
  calc
    _=∑ i : Fin 3,∑ j : Fin 3,if i=j then star (gauge E i)*(X*Y)*gauge E i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      calc
        _=star (gauge E i)*X*(gauge E i*star (gauge E j))*Y*gauge E j := by simp only [mul_assoc]
        _=_ := by
          rw [gauge_product]
          split_ifs with hij
          · subst j
            calc
              _=star (gauge E i)*(X*frame E)*Y*gauge E i := by simp only [mul_assoc]
              _=_ := by rw [hX]; simp only [mul_assoc]
          · simp
    _=_ := by simp

theorem spread_frame (E : SupportedScaffold P) : spread E (frame E)=E.supportA := by
  calc
    _=∑ i : Fin 3,frames E i := by
      apply Finset.sum_congr rfl
      intro i _
      change star (gauge E i)*frame E*gauge E i=_
      have hg : frame E*gauge E i=gauge E i := (gauge_block E i).1
      rw [mul_assoc,hg,(gauge_range E i).1]
    _=E.supportA := E.frame.1

theorem spread_supported (E : SupportedScaffold P) (X : Op) :
    E.supportA*spread E X=spread E X ∧ spread E X*E.supportA=spread E X := by
  have hs (i : Fin 3) : E.supportA*gauge E i=gauge E i ∧ gauge E i*E.supportA=gauge E i := by
    fin_cases i
    · exact projectionA_supported P E.strategy E.supportA E.supportA_laws.1 _
    · simpa [gauge] using graph_supported E.supportA (projectionA P E.strategy E.supportA)
        E.sharpA (projectionA_supported P E.strategy E.supportA E.supportA_laws.1) [] 0
    · simpa [gauge] using graph_supported E.supportA (projectionA P E.strategy E.supportA)
        E.sharpA (projectionA_supported P E.strategy E.supportA E.supportA_laws.1) [] 1
  have hstar (i : Fin 3) : E.supportA*star (gauge E i)=star (gauge E i) := by
    simpa only [star_mul,E.supportA_laws.1.1] using congrArg (fun A : Op => star A) (hs i).2
  constructor
  · simp only [spread,Finset.mul_sum,← mul_assoc,hstar]
  · simp only [spread,Finset.sum_mul,mul_assoc,hs]

theorem spread_commutant (E : SupportedScaffold P) (A : Op) (hA : star A=A)
    (hAF : Commute A (frame E)) (hAg : ∀ i,Commute A (gauge E i))
    (hAs : A*E.supportA=A) : spread E (A*frame E)=A := by
  calc
    _=∑ i : Fin 3,A*(star (gauge E i)*gauge E i) := by
      apply Finset.sum_congr rfl
      intro i _
      have hc : star (gauge E i)*A=A*star (gauge E i) := by
        simpa only [star_mul,hA] using congrArg (fun X : Op => star X) (hAg i).eq
      change star (gauge E i)*(A*frame E)*gauge E i=_
      have hg : frame E*gauge E i=gauge E i := (gauge_block E i).1
      rw [← mul_assoc,hc,mul_assoc,mul_assoc,hg]
    _=A*E.supportA := by simp only [gauge_range,← Finset.mul_sum,E.frame.1,frames]
    _=A := hAs

theorem spread_parameter (E : SupportedScaffold P) (p : Fin 25) :
    spread E (parameter E p.val*frame E)=parameter E p.val := by
  apply spread_commutant E _ (E.sharpA _).1 (E.parameter_frame p 0)
  · intro i
    fin_cases i
    · exact E.parameter_frame p 0
    · simpa [gauge] using (CompilerSoundnessJoints.parameter_graph P E.supportA
        (projectionA P E.strategy E.supportA) E.sharpA E.frame.2.1 E.rowsA p 0).2.2
    · simpa [gauge] using (CompilerSoundnessJoints.parameter_graph P E.supportA
        (projectionA P E.strategy E.supportA) E.sharpA E.frame.2.1 E.rowsA p 1).2.2
  · exact (projectionA_supported P E.strategy E.supportA E.supportA_laws.1 _).2

def fullValue (E : SupportedScaffold P) (p : Poly) : Op := spread E (value E p)

theorem value_supported (E : SupportedScaffold P) (p : Poly) :
    frame E*value E p=value E p ∧ value E p*frame E=value E p := by
  constructor
  · change frame E*(evalPoly (unitaries E) p*frame E)=_
    rw [← mul_assoc,(evalPoly_frame E p).eq,mul_assoc,(E.sharpA _).2]
    rfl
  · change (evalPoly (unitaries E) p*frame E)*frame E=_
    rw [mul_assoc,(E.sharpA _).2]
    rfl

theorem fullValue_mul (E : SupportedScaffold P) (p q : Poly) :
    fullValue E (mul p q)=fullValue E p*fullValue E q := by
  rw [fullValue,value_mul,spread_mul E _ _ (value_supported E p).2]
  rfl

theorem fullValue_e (E : SupportedScaffold P) (r : Fin 5) :
    fullValue E (e r.val)=parameter E (cornerIndex r.val) := by
  rw [fullValue,value_e]
  have hr : cornerIndex r.val<25 := by
    have := r.isLt; unfold cornerIndex; split_ifs <;> omega
  exact spread_parameter E ⟨cornerIndex r.val,hr⟩

theorem full_polynomial_equations (E : SupportedScaffold P) (p : Poly) (hp : p ∈ polynomials P) :
    fullValue E p=0 := by
  rw [fullValue,show value E p=0 from polynomial_equations E p hp,spread_zero]

#print axioms gauge_product
#print axioms spread_mul
#print axioms spread_frame
#print axioms spread_parameter
#print axioms fullValue_mul
#print axioms fullValue_e
#print axioms full_polynomial_equations
end Sigma2.CompilerSoundnessLift
