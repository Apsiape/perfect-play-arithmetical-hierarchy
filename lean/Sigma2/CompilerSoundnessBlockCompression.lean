import Sigma2.CompilerSoundnessAxisCompression
import Sigma2.CompilerSoundnessDictionary

/-! Literal full-support block equations, retaining all four axis words. -/
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessBlockCompression
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessBlockEquations CompilerSoundnessAxis
  CompilerSoundnessLift CompilerSoundnessDictionary CompilerSoundnessAxisCompression
  CompilerSoundnessCover
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

theorem spread_sum {ι : Type} (E : SupportedScaffold P) (s : Finset ι) (f : ι → Op) :
    spread E (∑ i ∈ s,f i)=∑ i ∈ s,spread E (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [spread_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,spread_add,ih]

theorem fullValue_corner (E : SupportedScaffold P) (i : Fin 25) :
    fullValue E (corner i.val)=parameter E i.val := by
  rw [fullValue,show value E (corner i.val)=parameter E i.val*frame E from eval_corner_frame E i]
  exact spread_parameter E i

theorem fullValue_magic (E : SupportedScaffold P) (g : Fin 4) :
    fullValue E (magic g.val)=magicSupport E g := by
  rw [fullValue,value_magic,magicSupport_eq,Finset.sum_mul,spread_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact spread_parameter E ⟨1+4*g.val+k.val,by have := g.isLt; have := k.isLt; omega⟩

theorem fullValue_axis (E : SupportedScaffold P) (g : Fin 4) (k : Fin 2) :
    fullValue E (axis g.val k.val)=axisOp E g k := by
  have hp := full_polynomial_equations E _ (show sub (axis g.val k.val)
      (one ++ scale (-2) (magic g.val) ++ scale 2 (axisParameter g.val k.val)) ∈ polynomials P from by
    simp only [polynomials,List.mem_append]; exact Or.inl (axis_structural_mem P g k))
  rw [fullValue_sub] at hp
  rw [sub_eq_zero.mp hp,fullValue_append,fullValue_append,fullValue_one,
    fullValue_scale,fullValue_scale,fullValue_magic]
  have hi : 17+2*g.val+k.val<25 := by have := g.isLt; have := k.isLt; omega
  have hc : fullValue E (axisParameter g.val k.val)=parameter E (17+2*g.val+k.val) := fullValue_corner E ⟨_,hi⟩
  rw [hc]
  have hx := cell_axis_parameter E g k
  unfold axisOp
  rw [← hx]
  norm_num only [Rat.cast_neg,Rat.cast_ofNat]
  module

def axisWord (E : SupportedScaffold P) (g : Fin 4) (k : ℕ) : Op :=
  (if k/2=0 then E.supportA else axisOp E g 0)*(if k%2=0 then E.supportA else axisOp E g 1)

theorem axisOp_supported (E : SupportedScaffold P) (g : Fin 4) (k : Fin 2) :
    E.supportA*axisOp E g k=axisOp E g k ∧ axisOp E g k*E.supportA=axisOp E g k := by
  rw [← fullValue_axis]
  exact fullValue_supported E _

theorem axisWord_values (E : SupportedScaffold P) (g : Fin 4) :
    axisWord E g 0=E.supportA ∧ axisWord E g 1=axisOp E g 1 ∧
      axisWord E g 2=axisOp E g 0 ∧ axisWord E g 3=axisOp E g 0*axisOp E g 1 := by
  norm_num [axisWord,E.supportA_laws.1.2,(axisOp_supported E g 0).2,(axisOp_supported E g 1).1]

theorem axisWord_source (E : SupportedScaffold P) (g : Fin 4) (k : Fin 4) :
    parameter E (cornerIndex g.val)*axisWord E g k.val=parameter E (cornerIndex g.val) ∧
      axisWord E g k.val*parameter E (cornerIndex g.val)=parameter E (cornerIndex g.val) := by
  have hs := projectionA_supported P E.strategy E.supportA E.supportA_laws.1 (.parameter (cornerIndex g.val))
  change E.supportA*parameter E (cornerIndex g.val)=_ ∧ parameter E (cornerIndex g.val)*E.supportA=_ at hs
  fin_cases k
  · rw [(axisWord_values E g).1]
    exact ⟨hs.2,hs.1⟩
  · rw [(axisWord_values E g).2.1]
    exact source_axis E g 1
  · rw [(axisWord_values E g).2.2.1]
    exact source_axis E g 0
  · rw [(axisWord_values E g).2.2.2]
    constructor
    · rw [← mul_assoc,(source_axis E g 0).1,(source_axis E g 1).1]
    · rw [mul_assoc,(source_axis E g 1).2,(source_axis E g 0).2]

theorem axisWord_target (E : SupportedScaffold P) (g : Fin 4) (k : Fin 4) :
    let C := parameter E (1+4*g.val)
    C*axisWord E g k.val*C=if k=0 then C else 0 := by
  have hs := projectionA_supported P E.strategy E.supportA E.supportA_laws.1 (.parameter (1+4*g.val))
  change E.supportA*parameter E (1+4*g.val)=_ ∧ parameter E (1+4*g.val)*E.supportA=_ at hs
  dsimp only
  fin_cases k
  · rw [(axisWord_values E g).1,hs.2,(E.sharpA _).2]
    rfl
  · rw [(axisWord_values E g).2.1,(target_axis_sandwich E g).2.1]
    rfl
  · rw [(axisWord_values E g).2.2.1,(target_axis_sandwich E g).1]
    rfl
  · rw [(axisWord_values E g).2.2.2,(target_axis_sandwich E g).2.2]
    rfl

theorem fullValue_transportTerm (E : SupportedScaffold P) (g : Fin 4) (l : ℕ) (k : ℕ) :
    fullValue E (transportTerm P g.val l k)=
      axisWord E g k*(parameter E (cornerIndex (g.val+1))*fullValue E (copyAtom P (g.val+1) l))*star (axisWord E g k) := by
  have hr : g.val+1<5 := by have := g.isLt; omega
  have ht : fullValue E (mul (if k/2=0 then one else axis g.val 0) (if k%2=0 then one else axis g.val 1))=axisWord E g k := by
    rw [fullValue_mul]
    unfold axisWord
    have ha0 : fullValue E (axis g.val 0)=axisOp E g 0 := fullValue_axis E g 0
    have ha1 : fullValue E (axis g.val 1)=axisOp E g 1 := fullValue_axis E g 1
    split_ifs <;> simp only [fullValue_one,ha0,ha1]
  unfold transportTerm
  rw [fullValue_mul,fullValue_mul,fullValue_adj,ht,fullValue_mul,fullValue_e E ⟨_,hr⟩]

/-- A projection compression which preserves the whole initial norm loses no
component. This supplies one-sided identities from the literal sandwiches. -/
theorem saturated_compression (C B : Op) (hC : Projection C)
    (h : star (C*B)*(C*B)=star B*B) : C*B=B := by
  have hz : star ((1-C)*B)*((1-C)*B)=0 := by
    have hs : star (C*B)*(C*B)=star B*C*B := by
      rw [star_mul,hC.1]
      calc
        _=star B*(C*C)*B := by simp only [mul_assoc]
        _=_ := by rw [hC.2]
    have hh : star B*C*B=star B*B := hs.symm.trans h
    rw [star_mul,(Compiler.projection_compl C hC).1]
    have hp := (Compiler.projection_compl C hC).2
    calc
      _=star B*((1-C)*(1-C))*B := by simp only [mul_assoc]
      _=star B*B-star B*C*B := by rw [hp,mul_sub,mul_one,sub_mul]
      _=0 := by rw [hh,sub_self]
  have hz' : (1-C)*B=0 := star_mul_self_eq_zero.mp hz
  rw [sub_mul,one_mul] at hz'
  exact (sub_eq_zero.mp hz').symm

#print axioms fullValue_axis
#print axioms axisWord_source
#print axioms axisWord_target
#print axioms fullValue_transportTerm
#print axioms saturated_compression
end Sigma2.CompilerSoundnessBlockCompression
