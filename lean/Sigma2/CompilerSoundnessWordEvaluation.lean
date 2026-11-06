import Sigma2.CompilerSoundnessWords
import Sigma2.CompilerScaffoldAlgebra

/-! One actual unitary dictionary evaluates every retained word consistently. -/
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessWordEvaluation
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessFrame CompilerSoundnessGraphs CompilerSoundnessJoints
  CompilerSoundnessTriangles CompilerSoundnessExtraction CompilerSoundnessWords
  CompilerSoundnessWordClosure Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
  CompilerScaffold.wordRows
variable {P : Presentation}

def unitaries (E : SupportedScaffold P) (i : ℕ) : Op :=
  if [(i,false)] ∈ words P then
    wordCorner E [(i,false)]+(1-projectionA P E.strategy E.supportA (.frame 0)) else 1

theorem unitaries_unitary (E : SupportedScaffold P) (i : ℕ) : Unitary (unitaries E i) := by
  unfold unitaries
  split_ifs with hi
  · exact wordCorner_completion E [(i,false)] hi
  · exact ⟨by rw [star_one,one_mul],by rw [star_one,one_mul]⟩

theorem unitaries_frame (E : SupportedScaffold P) (i : ℕ) :
    Commute (projectionA P E.strategy E.supportA (.frame 0)) (unitaries E i) := by
  let f := projectionA P E.strategy E.supportA (.frame 0)
  have hf : Projection f := E.sharpA _
  have hs : f*wordCorner E [(i,false)]=wordCorner E [(i,false)] ∧
      wordCorner E [(i,false)]*f=wordCorner E [(i,false)] := wordCorner_supported E _
  unfold unitaries
  split_ifs
  · change f*(_+(1-f))=(_+(1-f))*f
    rw [mul_add,add_mul,mul_sub,sub_mul,mul_one,one_mul,hf.2,hs.1,hs.2]
  · exact Commute.one_right _

theorem evalWord_frame (E : SupportedScaffold P) (w : Word) :
    Commute (projectionA P E.strategy E.supportA (.frame 0)) (evalWord (unitaries E) w) := by
  let f := projectionA P E.strategy E.supportA (.frame 0)
  have hf : star f=f := (E.sharpA _).1
  induction w with
  | nil => exact Commute.one_right _
  | cons t w ih =>
    change Commute f ((if t.2 then star (unitaries E t.1) else unitaries E t.1)*evalWord (unitaries E) w)
    apply Commute.mul_right _ ih
    cases t with
    | mk i b =>
      cases b
      · exact unitaries_frame E i
      · change f*star (unitaries E i)=star (unitaries E i)*f
        have hc : f*unitaries E i=unitaries E i*f := (unitaries_frame E i).eq
        have hh := congrArg (fun X : Op => star X) hc
        simpa only [star_mul,hf] using hh.symm

theorem inverse_rows (P : Presentation) (t : Token) (ht : [t] ∈ words P) :
    triangleRow [t] [(t.1,!t.2)] [] ∈ rowList P ∧
      triangleRow [(t.1,!t.2)] [t] [] ∈ rowList P := by
  constructor
  · apply wordRow_mem P [t] ht
    change triangleRow [t] [(t.1,!t.2)] [] ∈ CompilerScaffold.wordRows [t]
    unfold CompilerScaffold.wordRows
    apply List.mem_append_right
    exact List.mem_cons_self ..
  · apply wordRow_mem P [t] ht
    change triangleRow [(t.1,!t.2)] [t] [] ∈ CompilerScaffold.wordRows [t]
    unfold CompilerScaffold.wordRows
    apply List.mem_append_right
    exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem singleton_inverse (E : SupportedScaffold P) (t : Token) (ht : [t] ∈ words P) :
    wordCorner E [(t.1,!t.2)]=star (wordCorner E [t]) := by
  let f := fun i : Fin 3 => projectionA P E.strategy E.supportA (.frame i.val)
  let V := wordCorner E [t]
  let W := wordCorner E [(t.1,!t.2)]
  have ht' : [(t.1,!t.2)] ∈ words P := (words_singletons P [t] ht t (by simp)).2
  have hp : V*W=f 0 := (wordCorner_composition E [t] [(t.1,!t.2)] [] ht ht'
    (empty_mem_words P) (inverse_rows P t ht).1).trans (wordCorner_empty E)
  have hu : star V*V=f 0 := (wordCorner_unitary E [t] ht).1
  have hs : f 0*W=W := (wordCorner_supported E _).1
  have hvs : FrameBlock f 0 0 (star V) := block_star f (fun i => E.sharpA _) 0 0 V (wordCorner_supported E _)
  calc
    W=f 0*W := hs.symm
    _=(star V*V)*W := by rw [hu]
    _=star V*(V*W) := mul_assoc _ _ _
    _=star V := by rw [hp,hvs.2]

theorem positive_on_frame (E : SupportedScaffold P) (i : ℕ) (hi : [(i,false)] ∈ words P) :
    unitaries E i*projectionA P E.strategy E.supportA (.frame 0)=wordCorner E [(i,false)] := by
  let f := projectionA P E.strategy E.supportA (.frame 0)
  have hf : Projection f := E.sharpA _
  have hs : wordCorner E [(i,false)]*f=wordCorner E [(i,false)] := (wordCorner_supported E _).2
  rw [unitaries,if_pos hi]
  change (_+(1-f))*f=_
  rw [add_mul,sub_mul,one_mul,hf.2,sub_self,add_zero,hs]

theorem singleton_eval (E : SupportedScaffold P) (t : Token) (ht : [t] ∈ words P) :
    evalWord (unitaries E) [t]*projectionA P E.strategy E.supportA (.frame 0)=wordCorner E [t] := by
  cases t with
  | mk i b =>
    cases b
    · simpa only [evalWord,Bool.false_eq_true,ite_false,mul_one] using positive_on_frame E i ht
    · let f := fun k : Fin 3 => projectionA P E.strategy E.supportA (.frame k.val)
      have hf : Projection (f 0) := E.sharpA _
      have hi : [(i,false)] ∈ words P := by
        simpa using (words_singletons P [(i,true)] ht (i,true) (by simp)).2
      have hv : FrameBlock f 0 0 (star (wordCorner E [(i,false)])) :=
        block_star f (fun k => E.sharpA _) 0 0 _ (wordCorner_supported E _)
      have ha : wordCorner E [(i,true)]=star (wordCorner E [(i,false)]) := singleton_inverse E (i,false) hi
      simp only [evalWord,ite_true,mul_one]
      rw [unitaries,if_pos hi]
      change star (_+(1-f 0))*f 0=_
      rw [star_add _ (1-f 0),star_sub (1:Op) (f 0),star_one,hf.1,
        add_mul,sub_mul,one_mul,hf.2,sub_self,add_zero,hv.2,ha]

theorem product_row (P : Presentation) (u : Word) (t : Token) (hu : u≠[])
    (hw : u++[t] ∈ words P) : triangleRow u [t] (u++[t]) ∈ rowList P := by
  apply wordRow_mem P (u++[t]) hw
  change triangleRow u [t] (u++[t]) ∈ CompilerScaffold.wordRows (u++[t])
  unfold CompilerScaffold.wordRows
  apply List.mem_append_left
  apply List.mem_append_right
  have hlen : (u++[t]).length>1 := by
    have hn : 0<u.length := List.length_pos_iff.mpr hu
    simp only [List.length_append,List.length_singleton]
    omega
  rw [if_pos hlen]
  have htake : (u++[t]).take ((u++[t]).length-1)=u := by simp
  have hdrop : (u++[t]).drop ((u++[t]).length-1)=[t] := by simp
  rw [htake,hdrop]
  exact List.mem_cons_self ..

/-- The frozen evalWord evaluates every retained word in the same actual frame. -/
theorem evalWord_retained (E : SupportedScaffold P) (w : Word) (hw : w ∈ words P) :
    evalWord (unitaries E) w*projectionA P E.strategy E.supportA (.frame 0)=wordCorner E w := by
  let f := projectionA P E.strategy E.supportA (.frame 0)
  have hf : Projection f := E.sharpA _
  induction w using List.reverseRecOn with
  | nil => simpa only [evalWord,one_mul] using (wordCorner_empty E).symm
  | append_singleton u t ih =>
    by_cases hu : u=[]
    · subst u
      exact singleton_eval E t hw
    · have hp : u ∈ words P := by simpa using words_take P (u++[t]) hw u.length
      have ht : [t] ∈ words P := (words_singletons P (u++[t]) hw t (by simp)).1
      rw [evalWord_append]
      calc
        _=(evalWord (unitaries E) u*f)*(evalWord (unitaries E) [t]*f) := by
          symm
          calc
            _=evalWord (unitaries E) u*(f*evalWord (unitaries E) [t])*f := by noncomm_ring
            _=evalWord (unitaries E) u*(evalWord (unitaries E) [t]*f)*f := by rw [(evalWord_frame E [t]).eq]
            _=(evalWord (unitaries E) u*evalWord (unitaries E) [t])*(f*f) := by noncomm_ring
            _=_ := by rw [hf.2]
        _=wordCorner E u*wordCorner E [t] := by rw [ih hp,singleton_eval E t ht]
        _=wordCorner E (u++[t]) := wordCorner_composition E u [t] (u++[t]) hp ht hw (product_row P u t hu hw)

theorem one_unitary_dictionary (E : SupportedScaffold P) :
    ∃ U : ℕ → Op,(∀ i,Unitary (U i)) ∧
      ∀ w ∈ words P,evalWord U w*projectionA P E.strategy E.supportA (.frame 0)=wordCorner E w :=
  ⟨unitaries E,unitaries_unitary E,evalWord_retained E⟩

#print axioms singleton_inverse
#print axioms evalWord_retained
#print axioms one_unitary_dictionary
end Sigma2.CompilerSoundnessWordEvaluation
