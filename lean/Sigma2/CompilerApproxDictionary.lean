import Sigma2.CompilerHonestDictionaryAssembly
import Sigma2.CompilerEventSlots

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxDictionary
open Compiler CompilerScaffold CompilerHonestDictionary CompilerFiniteRegister
  CompilerHonestLift CompilerHonestLabels CompilerHonestSyntax FiniteAncilla

 theorem lift_add (d : ℕ) [NeZero d] (a b : Fin d) (A B : Op) :
    lift d a b (A+B)=lift d a b A+lift d a b B := by
  unfold lift
  rw [show CompilerApproxBlocks.singleBlocks d a b (A+B)=
    CompilerApproxBlocks.singleBlocks d a b A+CompilerApproxBlocks.singleBlocks d a b B by
      ext i j; simp [CompilerApproxBlocks.singleBlocks,ite_add_ite]]
  exact matrixOp_add d _ _

 theorem lift_smul (d : ℕ) [NeZero d] (a b : Fin d) (c : ℂ) (A : Op) :
    lift d a b (c • A)=c • lift d a b A := by
  unfold lift
  rw [show CompilerApproxBlocks.singleBlocks d a b (c • A)=
    c • CompilerApproxBlocks.singleBlocks d a b A by
      ext i j; by_cases hi : i=a <;> by_cases hj : j=b <;>
        simp [CompilerApproxBlocks.singleBlocks,hi,hj]]
  exact matrixOp_smul d c _

 theorem corner_lift (d : ℕ) [NeZero d] (a : Fin d) :
    CompilerFiniteRegister.corner d a=lift d a a 1 := by
  unfold CompilerFiniteRegister.corner diagonal lift
  congr 1
  ext i j
  by_cases hi : i=a <;> by_cases hj : j=a <;> by_cases hij : i=j <;>
    simp_all [Matrix.diagonal_apply,CompilerApproxBlocks.singleBlocks]

 theorem corner_copy (d : ℕ) [NeZero d] (a : Fin d) (U : Op) :
    CompilerFiniteRegister.corner d a*copy d a U=lift d a a U := by
  rw [CompilerFiniteRegister.corner,copy,diagonal_mul]
  unfold diagonal lift
  congr 1
  ext i j
  by_cases hi : i=a <;> by_cases hj : j=a <;> by_cases hij : i=j <;>
    simp_all [Matrix.diagonal_apply,CompilerApproxBlocks.singleBlocks]

 theorem eval_e {P : Presentation} (R : StructuralRealization P) (k : ℕ) (hk : k<5) :
    evalPoly (dictionary R) (e k)=CompilerFiniteRegister.corner 17 (selected k) := by
  have hci : cornerIndex k<17 := by
    dsimp [cornerIndex]; split_ifs <;> omega
  rw [e,eval_corner]
  have hd : dictionary R (cornerIndex k)=reflection (CompilerFiniteRegister.corner 17 ⟨cornerIndex k,hci⟩) := by
    simp only [dictionary,dif_pos (show cornerIndex k<25 by omega),parameter,dif_pos hci]
  rw [hd]
  have hs : selected k=⟨cornerIndex k,hci⟩ := by simp [selected,hk]
  rw [hs,reflection]
  module

 theorem offset_lt (P : Presentation) (i : Fin P.types.length) : encodingOffset P i.val<encodingCount P := by
  change ((P.types.take i.val).map (fun t => if t=LabelType.contraction then 2 else 1)).sum<
    (P.types.map (fun t => if t=LabelType.contraction then 2 else 1)).sum
  have hp : ∀ t ∈ P.types,0<((if t=LabelType.contraction then 2 else 1 : ℕ)) := by
    intro t ht; split_ifs <;> omega
  have hd := List.take_append_drop i.val P.types
  have hd' : P.types.drop i.val≠[] := by
    intro hh; have := List.drop_eq_nil_iff.mp hh; omega
  have hpos : 0<((P.types.drop i.val).map (fun t => (if t=LabelType.contraction then 2 else 1 : ℕ))).sum := by
    cases he : P.types.drop i.val with
    | nil => exact False.elim (hd' he)
    | cons t ts => simp only [List.map_cons,List.sum_cons]; split_ifs <;> omega
  have heq := congrArg (fun xs : List LabelType =>
    (xs.map (fun t => (if t=LabelType.contraction then 2 else 1 : ℕ))).sum) hd
  simp only [List.map_append,List.sum_append] at heq
  omega

 theorem dictionary_copy {P : Presentation} (R : StructuralRealization P)
    (k l : ℕ) (hk : k<5) (hl : l<encodingCount P) :
    dictionary R (33+k*encodingCount P+l)=copy 17 (selected k) (encoding R l) := by
  have hc : 0<encodingCount P := by omega
  have hn : 33+k*encodingCount P+l<33+5*encodingCount P := by nlinarith
  simp only [dictionary]
  rw [dif_neg (by omega),dif_neg (by omega),if_pos hn]
  have hs : 33+k*encodingCount P+l-33=k*encodingCount P+l := by omega
  rw [hs,Nat.mul_comm k (encodingCount P),Nat.mul_add_div hc,Nat.div_eq_of_lt hl,Nat.add_zero,
    Nat.mul_add_mod,Nat.mod_eq_of_lt hl]

 theorem fix_commute (e U : Op) (he : Projection e) (hu : Unitary U)
    (hf : (U-1)*(1-e)=0) : Commute e U := by
  have hq : U*(1-e)=1-e := by
    have ht : U*(1-e)-(1-e)=0 := by simpa only [sub_mul,one_mul] using hf
    exact sub_eq_zero.mp ht
  have hqs : (1-e)*star U=1-e := by
    have ht := congrArg (fun A : Op => star A) hq
    simpa only [star_mul,star_sub (1:Op) e,star_one,he.1] using ht
  have hqr : (1-e)*U=1-e := by
    have ht := congrArg (fun A : Op => A*U) hqs
    simpa only [mul_assoc,hu.1,mul_one] using ht.symm
  change e*U=U*e
  have hl : U-e*U=1-e := by simpa only [sub_mul,one_mul] using hqr
  have hr : U-U*e=1-e := by simpa only [mul_sub,mul_one] using hq
  exact sub_right_inj.mp (hl.trans hr.symm)

 def labelExtension {P : Presentation} (R : StructuralRealization P) (i : ℕ) : Op :=
  decodeEncoding 1 (encoding R (encodingOffset P i))
    (encoding R (encodingOffset P i+1)) ((P.types[i]?).getD .unitary)

 theorem labelExtension_compress {P : Presentation} (R : StructuralRealization P)
    (i : Fin P.types.length) :
    R.support*labelExtension R i.val=R.label i.val ∧
    labelExtension R i.val*R.support=R.label i.val := by
  have hU := fix_commute R.support _ R.support_projection
    (encoding_properties R (encodingOffset P i.val)).1
    (encoding_properties R (encodingOffset P i.val)).2.2
  have hV := fix_commute R.support _ R.support_projection
    (encoding_properties R (encodingOffset P i.val+1)).1
    (encoding_properties R (encodingOffset P i.val+1)).2.2
  have hUs : Commute R.support (star (encoding R (encodingOffset P i.val))) := by
    have ht := congrArg (fun A : Op => star A) hU.eq
    simpa only [Commute,SemiconjBy,star_mul,R.support_projection.1] using ht.symm
  have hd := (encodings_properties R).2.2 i |>.1
  change decodeEncoding R.support (encoding R (encodingOffset P i.val))
    (encoding R (encodingOffset P i.val+1)) P.types[i.val]=R.label i.val at hd
  have ht : (P.types[i.val]?).getD .unitary=P.types[i.val] := by simp
  have hc : Commute R.support (labelExtension R i.val) := by
    rw [labelExtension,ht]
    cases P.types[i.val] <;> dsimp only [decodeEncoding] <;> simp only [one_mul]
    · exact hU
    · exact ((Commute.one_right _).add_right hU).smul_right _
    · exact (((Commute.one_right _).smul_right _).add_right hU |>.add_right hUs).smul_right _
    · exact (hU.add_right hV).smul_right _
  have hl : R.support*labelExtension R i.val=R.label i.val := by
    rw [labelExtension,ht]
    cases ht : P.types[i.val] <;> simpa only [ht,decodeEncoding,one_mul] using hd
  exact ⟨hl,hc.eq.symm.trans hl⟩

#print axioms eval_e
#print axioms dictionary_copy
#print axioms labelExtension_compress
end Sigma2.CompilerApproxDictionary
