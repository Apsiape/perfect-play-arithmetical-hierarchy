import Sigma2.CompilerHonestAllocation
import Sigma2.CompilerFiniteRegister

/-! One simultaneous dictionary at every literal frozen atom number. The
seventeen corners, eight axis parameters, eight axes, all label copies and
blocks, and all four two-unitary creation encodings share one register. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestDictionary
open Compiler CompilerScaffold CompilerHonestLift CompilerFiniteRegister
  CompilerHonestAllocation CompilerHonestDensity

def parameter (n : ℕ) : Op :=
  if hn : n<17 then corner 17 ⟨n,hn⟩
  else if hn : n<25 then
    positiveAxis ⟨(n-17)/2,by omega⟩ ⟨(n-17)%2,by omega⟩
  else 0

theorem parameter_projection (n : ℕ) : Projection (parameter n) := by
  dsimp only [parameter]
  split_ifs
  · exact corner_projection 17 _
  · exact positiveAxis_projection _ _
  · exact ⟨star_zero Op,mul_zero 0⟩

def reflection (P : Op) : Op := (2:ℂ) • P-1

theorem reflection_unitary (P : Op) (hP : Projection P) : Unitary (reflection P) := by
  have hs : star (reflection P)=reflection P := by
    dsimp only [reflection]
    rw [star_sub ((2:ℂ) • P) (1:Op),star_smul (2:ℂ) P,hP.1,star_one]
    norm_num
  have hsq : reflection P*reflection P=1 := by
    simp only [reflection,sub_mul,mul_sub,smul_mul_smul_comm,smul_mul_assoc,
      mul_smul_comm,mul_one,one_mul,hP.2]
    module
  exact ⟨by rw [hs,hsq],by rw [hs,hsq]⟩

def encodings {P : Presentation} (R : StructuralRealization P) : List Op :=
  Classical.choose (label_allocation R)

theorem encodings_properties {P : Presentation} (R : StructuralRealization P) :
    (encodings R).length=encodingCount P ∧
    (∀ U ∈ encodings R,Unitary U ∧ Centralizes R.density.op U ∧ (U-1)*(1-R.support)=0) ∧
    (∀ i : Fin P.types.length,
      CompilerHonestLabels.decodeEncoding R.support
        ((encodings R)[encodingOffset P i.val]?.getD 1)
        ((encodings R)[encodingOffset P i.val+1]?.getD 1) P.types[i.val]=R.label i.val ∧
      (P.types[i.val]=.projection →
        ((encodings R)[encodingOffset P i.val]?.getD 1)*
          ((encodings R)[encodingOffset P i.val]?.getD 1)=1)) :=
  Classical.choose_spec (label_allocation R)

def encoding {P : Presentation} (R : StructuralRealization P) (i : ℕ) : Op :=
  ((encodings R)[i]?).getD 1

theorem encoding_properties {P : Presentation} (R : StructuralRealization P) (i : ℕ) :
    Unitary (encoding R i) ∧ Centralizes R.density.op (encoding R i) ∧
      (encoding R i-1)*(1-R.support)=0 := by
  cases he : (encodings R)[i]? with
  | none => simp [encoding,he,Unitary,Centralizes]
  | some A =>
      simpa only [encoding,he,Option.getD_some] using
        (encodings_properties R).2.1 A (List.mem_of_getElem? he)

def creationU {P : Presentation} (R : StructuralRealization P) : Fin 4 → Op :=
  Classical.choose (creation_encodings R)

def creationV {P : Presentation} (R : StructuralRealization P) : Fin 4 → Op :=
  Classical.choose (Classical.choose_spec (creation_encodings R))

theorem creation_properties {P : Presentation} (R : StructuralRealization P) :
    (∀ a,Unitary (creationU R a) ∧ Unitary (creationV R a)) ∧
    (∀ a,Centralizes (scaffoldDensity R.density).op (creationU R a) ∧
      Centralizes (scaffoldDensity R.density).op (creationV R a)) ∧
    (∀ a,lift 17 13 0 (R.creation a)=(1/2:ℂ) • (creationU R a+creationV R a)) :=
  Classical.choose_spec (Classical.choose_spec (creation_encodings R))

/-- The five selected scalar corners, with harmless totalization elsewhere. -/
def selected (r : ℕ) : Fin 17 :=
  ⟨if r<5 then cornerIndex r else 0,by
    split_ifs with hr
    · dsimp [cornerIndex]
      split_ifs <;> omega
    · omega⟩

def bridgeActive (g : ℕ) (i : Fin 17) : Bool :=
  decide ((i = selected g) ∨ (((1 + 4 * g : ℕ) ≤ i.val) ∧ (i.val < (5 + 4 * g : ℕ))))

/-- Every atom in the actual frozen allocation has one simultaneous value. -/
def dictionary {P : Presentation} (R : StructuralRealization P) (n : ℕ) : Op :=
  if hn : n<25 then reflection (parameter n)
  else if hn : n<33 then axisUnitary ⟨(n-25)/2,by omega⟩ ⟨(n-25)%2,by omega⟩
  else if n<33+5*encodingCount P then
    copy 17 (selected ((n-33)/encodingCount P)) (encoding R ((n-33)%encodingCount P))
  else if n<33+9*encodingCount P then
    repeated 17 (bridgeActive ((n-33-5*encodingCount P)/encodingCount P))
      (encoding R ((n-33-5*encodingCount P)%encodingCount P))
  else if hn : n<33+9*encodingCount P+8 then
    if (n-33-9*encodingCount P)%2=0 then
      creationU R ⟨(n-33-9*encodingCount P)/2,by omega⟩
    else creationV R ⟨(n-33-9*encodingCount P)/2,by omega⟩
  else 1

theorem dictionary_unitary {P : Presentation} (R : StructuralRealization P) (n : ℕ) :
    Unitary (dictionary R n) := by
  dsimp only [dictionary]
  split_ifs
  · exact reflection_unitary _ (parameter_projection n)
  · exact axisUnitary_unitary _ _
  · exact copy_unitary 17 _ _ (encoding_properties R _).1
  · exact repeat_unitary 17 _ _ (encoding_properties R _).1
  · exact (creation_properties R).1 _ |>.1
  · exact (creation_properties R).1 _ |>.2
  · simp [Unitary]

#print axioms encodings_properties
#print axioms creation_properties
#print axioms dictionary_unitary

theorem parameter_centralizer (h : Density) (n : ℕ) :
    Centralizes (scaffoldDensity h).op (parameter n) := by
  dsimp only [parameter]
  split_ifs with hn17 hn25
  · exact corner_centralizer 17 _ _ _
  · let g : Fin 4 := ⟨(n-17)/2,by omega⟩
    let k : Fin 2 := ⟨(n-17)%2,by omega⟩
    change Centralizes (scaffoldDensity h).op (positiveAxis g k)
    dsimp only [positiveAxis]
    have hm : Centralizes (scaffoldDensity h).op (mask 17 (magicActive g)) := by
      apply diagonal_centralizer
      intro i
      split_ifs <;> simp [Centralizes]
    exact (show Commute _ _ from hm).mul_right
      (((Commute.one_right _).add_right (axisUnitary_centralizer h g k)).smul_right (1/2:ℂ))
  · simp [Centralizes]

theorem dictionary_centralizer {P : Presentation} (R : StructuralRealization P) (n : ℕ) :
    Centralizes (scaffoldDensity R.density).op (dictionary R n) := by
  dsimp only [dictionary]
  split_ifs
  · exact ((show Commute _ _ from parameter_centralizer R.density n).smul_right
      (2:ℂ)).sub_right (Commute.one_right _)
  · exact axisUnitary_centralizer _ _ _
  · exact copy_centralizer 17 _ _ _ _ (encoding_properties R _).2.1
  · exact repeat_centralizer 17 _ _ _ _ (encoding_properties R _).2.1
  · exact (creation_properties R).2.1 _ |>.1
  · exact (creation_properties R).2.1 _ |>.2
  · simp [Centralizes]

/-- The actual four `creation` polynomials decode to the intended rectangular
lifts in this one dictionary, including their literal 33+9c+2a allocation. -/
theorem eval_creation {P : Presentation} (R : StructuralRealization P) (a : Fin 4) :
    evalPoly (dictionary R) (creation P a.val)=lift 17 13 0 (R.creation a) := by
  have he (k : Fin 8) :
      dictionary R (33+9*encodingCount P+k.val)=
        if k.val%2=0 then creationU R ⟨k.val/2,by have := k.isLt; omega⟩
        else creationV R ⟨k.val/2,by have := k.isLt; omega⟩ := by
    have hk := k.isLt
    simp only [dictionary]
    rw [dif_neg (by omega),dif_neg (by omega),if_neg (by omega),if_neg (by omega),
      dif_pos (by omega)]
    have ht : 33+9*encodingCount P+k.val-33-9*encodingCount P=k.val := by omega
    simp only [ht]
  rw [creation,evalPoly_scale,evalPoly_append,CompilerHonestSyntax.eval_atom,
    CompilerHonestSyntax.eval_atom]
  have hu := he ⟨2*a.val,by have := a.isLt; omega⟩
  have hv := he ⟨2*a.val+1,by have := a.isLt; omega⟩
  have hnext : 34+9*encodingCount P+2*a.val=33+9*encodingCount P+(2*a.val+1) := by omega
  rw [hnext]
  have hmod0 : (2*a.val)%2=0 := by omega
  have hmod1 : (2*a.val+1)%2=1 := by omega
  have hdiv0 : (2*a.val)/2=a.val := by omega
  have hdiv1 : (2*a.val+1)/2=a.val := by omega
  have hu' : dictionary R (33+9*encodingCount P+2*a.val)=creationU R a := by
    simpa only [hmod0,hdiv0,Fin.eta,ite_true] using hu
  have hv' : dictionary R (33+9*encodingCount P+(2*a.val+1))=creationV R a := by
    simpa only [hmod1,hdiv1,Fin.eta,show (1:ℕ)≠0 by decide,ite_false] using hv
  rw [hu',hv']
  norm_num
  simpa only [smul_add] using ((creation_properties R).2.2 a).symm

#print axioms dictionary_centralizer
#print axioms eval_creation

end Sigma2.CompilerHonestDictionary
