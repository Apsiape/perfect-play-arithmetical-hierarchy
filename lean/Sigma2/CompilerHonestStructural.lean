import Sigma2.CompilerHonestTransport

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestStructural
open Compiler CompilerScaffold CompilerHonestDictionary CompilerFiniteRegister
  CompilerHonestLift CompilerHonestSyntax CompilerApproxDictionary
  CompilerApproxResidual CompilerRegisterIdentities CompilerHonestTransport FiniteAncilla

theorem copy_outside (d : ℕ) [NeZero d] (a : Fin d) (U : Op) :
    (copy d a U-1)*(1-CompilerFiniteRegister.corner d a)=0 := by
  calc
    _=diagonal d (fun i => ((if i=a then U else 1)-1)*(1-(if i=a then 1 else 0))) := by
      rw [← diagonal_mul,diagonal_sub,diagonal_sub,diagonal_one]
      rfl
    _=diagonal d (fun _ => (0:Op)) := by
      congr 1
      funext i
      split_ifs <;> simp
    _=0 := (diagLinear d).map_zero

theorem copy_square (d : ℕ) [NeZero d] (a : Fin d) (U : Op) (hU : U*U=1) :
    copy d a U*copy d a U=1 := by
  rw [copy,diagonal_mul]
  calc
    _=diagonal d (fun _ => (1:Op)) := by
      congr 1
      funext i
      split_ifs <;> simp [hU]
    _=1 := diagonal_one d

theorem parameter_square {P : Presentation} (R : StructuralRealization P) (i : Fin 25) :
    dictionary R i.val*dictionary R i.val=1 := by
  have hd : dictionary R i.val=reflection (parameter i.val) := by
    simp only [dictionary,dif_pos i.isLt]
  have hs : star (dictionary R i.val)=dictionary R i.val := by
    rw [hd,reflection,star_sub ((2:ℂ) • parameter i.val) (1:Op),star_smul (2:ℂ) (parameter i.val),(parameter_projection i.val).1,star_one]
    norm_num
  simpa only [hs] using (dictionary_unitary R i.val).1

theorem axis_equation (g : Fin 4) (k : Fin 2) :
    axisUnitary g k-(1+(-2:ℂ) • mask 17 (magicActive g)+(2:ℂ) • positiveAxis g k)=0 := by
  have he : 1+(-2:ℂ) • mask 17 (magicActive g)+(2:ℂ) • positiveAxis g k=
      1-mask 17 (magicActive g)+mask 17 (magicActive g)*axisUnitary g k := by
    simp only [positiveAxis,mul_smul_comm,mul_add,mul_one,smul_add,smul_smul]
    module
  rw [he]
  exact sub_eq_zero.mpr (axis_outside g k)

theorem creation_equation {P : Presentation} (R : StructuralRealization P) (a : Fin 4) :
    evalPoly (dictionary R) (CompilerScaffold.sub (creation P a.val)
      (CompilerScaffold.mul (CompilerScaffold.mul (e 4) (creation P a.val)) (e 0)))=0 := by
  rw [evalPoly_sub,evalPoly_mul,evalPoly_mul,eval_creation R a,eval_e R 4 (by norm_num),
    eval_e R 0 (by norm_num),corner_lift,corner_lift]
  change lift 17 13 0 (R.creation a)-(lift 17 13 13 1*lift 17 13 0 (R.creation a))*lift 17 0 0 1=0
  simp [lift_mul]

/-- Every literal structural polynomial vanishes globally in the simultaneous dictionary. -/
theorem structural_zero {P : Presentation} (R : StructuralRealization P)
    (p : Poly) (hp : p ∈ structuralPolynomials P) : evalPoly (dictionary R) p=0 := by
  simp only [structuralPolynomials,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
    List.mem_map,List.mem_flatMap,List.mem_range,List.mem_filterMap] at hp
  rcases hp with ((((((hp|hp)|hp)|hp)|hp)|hp)|hp)
  · subst p
    rw [evalPoly_sub,eval_sum_range,eval_one]
    have he : (∑ i : Fin 17,evalPoly (dictionary R) (CompilerScaffold.corner i.val))=
        ∑ i : Fin 17,CompilerFiniteRegister.corner 17 i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [eval_parameter R _ (by have := i.isLt; omega)]
      simp only [parameter,dif_pos i.isLt]
    rw [he,corners_total,sub_self]
  · obtain ⟨i,hi,rfl⟩ := hp
    rw [evalPoly_sub,evalPoly_mul,eval_atom,eval_one,parameter_square R ⟨i,hi⟩,sub_self]
  · obtain ⟨g,hg,k,hk,rfl⟩ := hp
    rw [evalPoly_sub,eval_axis R ⟨g,hg⟩ ⟨k,hk⟩,evalPoly_append,evalPoly_append,
      eval_one,evalPoly_scale,evalPoly_scale,eval_magic R ⟨g,hg⟩,eval_axis_parameter R ⟨g,hg⟩ ⟨k,hk⟩]
    norm_num
    exact axis_equation ⟨g,hg⟩ ⟨k,hk⟩
  · obtain ⟨k,hk,l,hl,rfl⟩ := hp
    rw [evalPoly_mul,evalPoly_sub,evalPoly_sub,copyAtom,eval_atom,eval_one,
      eval_e R k hk,dictionary_copy R k l hk hl]
    exact copy_outside 17 _ _
  · obtain ⟨k,hk,i,hi,hp⟩ := hp
    split_ifs at hp with ht
    · have he := Option.some.inj hp
      subst p
      obtain ⟨hilt,hit⟩ := List.getElem?_eq_some_iff.mp ht
      have hs := (encodings_properties R).2.2 ⟨i,hilt⟩ |>.2 hit
      rw [evalPoly_sub,evalPoly_mul,copyAtom,eval_atom,eval_one,
        dictionary_copy R k _ hk (offset_lt P ⟨i,hilt⟩)]
      exact sub_eq_zero.mpr (copy_square 17 _ _ hs)
  · obtain ⟨g,hg,l,hl,rfl⟩ := hp
    exact eval_block_equation R ⟨g,hg⟩ ⟨l,hl⟩
  · obtain ⟨a,ha,rfl⟩ := hp
    exact creation_equation R ⟨a,ha⟩

theorem structural_supported {P : Presentation} (R : StructuralRealization P)
    (p : Poly) (hp : p ∈ structuralPolynomials P) :
    evalPoly (dictionary R) p*(CompilerHonestDensity.scaffoldDensity R.density).op=0 := by
  rw [structural_zero R p hp,zero_mul]

#print axioms structural_zero
#print axioms structural_supported
end Sigma2.CompilerHonestStructural
