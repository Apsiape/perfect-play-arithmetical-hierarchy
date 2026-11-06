import Sigma2.CompilerApproxResidual

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxMatching
open Compiler CompilerScaffold CompilerHonestDictionary CompilerHonestLift
  CompilerApproxDictionary CompilerApproxLabels CompilerApproxResidual
  CompilerHonestDensity CompilerApproxBlocks FiniteAncilla

abbrev Entry := Poly × Fin 17 × Fin 17 × Op

def entries (P : Presentation) (R : StructuralRealization P) : List Entry :=
  (List.ofFn (fun a : Fin 4 => a)).flatMap (fun a => List.ofFn (fun b : Fin 4 =>
    (sub (mul (adj (creation P a.val)) (creation P b.val)) (if a.val=b.val then e 0 else []),
      0,0,star (R.creation a)*R.creation b-(if a=b then R.support else 0)))) ++
  [(sub (sum ((List.range 4).map (fun a => mul (creation P a) (adj (creation P a)))))
      (sub (e 4) (labelCopy P 4 P.root)),13,13,
    (∑ a,R.creation a*star (R.creation a))-(R.support-R.label P.root))] ++
  P.central.map (fun p => (expression P 0 p,0,0,p.eval R.support R.label)) ++
  P.endpoints.map (fun t => (sub (mul (expression P 4 t.1) (creation P t.2.1.val))
    (mul (creation P t.2.2.1.val) (expression P 0 t.2.2.2)),13,0,
    t.1.eval R.support R.label*R.creation t.2.1-R.creation t.2.2.1*t.2.2.2.eval R.support R.label)) ++
  P.zeros.map (fun t => (mul (expression P 4 t.1) (creation P t.2.val),13,0,
    t.1.eval R.support R.label*R.creation t.2)) ++
  P.linear.map (fun row => (sum (row.map (fun t =>
    mul (mul (expression P 4 t.1) (creation P t.2.1.val)) (expression P 0 t.2.2))),13,0,
    (row.map (fun t => t.1.eval R.support R.label*R.creation t.2.1*t.2.2.eval R.support R.label)).sum))

 theorem entries_polynomials (P : Presentation) (R : StructuralRealization P) :
    (entries P R).map Prod.fst=applicationPolynomials P := by
  simp only [entries,applicationPolynomials,List.map_append,List.map_flatMap,List.map_ofFn,
    List.map_map,Function.comp_def,List.map_cons,List.map_nil]
  rfl

 theorem entries_residuals (P : Presentation) (R : StructuralRealization P) :
    (entries P R).map (fun t => t.2.2.2)=applicationResiduals P R := by
  simp only [entries,applicationResiduals,List.map_append,List.map_flatMap,List.map_ofFn,
    List.map_map,Function.comp_def,List.map_cons,List.map_nil]

 theorem entries_length (P : Presentation) (R : StructuralRealization P) :
    (entries P R).length=(applicationPolynomials P).length := by
  simpa only [List.length_map] using congrArg List.length (entries_polynomials P R)

 theorem entry_compress (P : Presentation) (hP : P.admissible) (R : StructuralRealization P)
    (t : Entry) (ht : t∈entries P R) :
    evalPoly (dictionary R) t.1*amplify 17 R.support=lift 17 t.2.1 t.2.2.1 t.2.2.2 := by
  have htransport (i : ℕ) (hi : i∈P.transported) : i<P.types.length := hP.2.1 i hi
  simp only [entries,List.mem_append] at ht
  rcases ht with (((((hi|hr)|hc)|he)|hz)|hl)
  · obtain ⟨a,ha,ht⟩ := List.mem_flatMap.mp hi
    obtain ⟨b,hb⟩ := List.mem_ofFn.mp ht
    subst t
    exact isometry_compress R a b
  · have ht : t=(sub (sum ((List.range 4).map (fun a => mul (creation P a) (adj (creation P a)))))
      (sub (e 4) (labelCopy P 4 P.root)),13,13,
      (∑ a,R.creation a*star (R.creation a))-(R.support-R.label P.root)) := by simpa using hr
    subst t
    have hroot : P.root<P.types.length := List.getElem?_eq_some_iff.mp hP.1 |>.1
    exact range_compress R hroot
  · obtain ⟨p,hp,ht⟩ := List.mem_map.mp hc
    subst t
    exact central_compress R p (hP.2.2.1 p hp)
  · obtain ⟨r,hr,ht⟩ := List.mem_map.mp he
    subst t
    obtain ⟨hp,hq⟩ := hP.2.2.2.1 r hr
    exact endpoint_compress R _ _ _ _ (fun i hi => htransport i (hp i hi)) hq
  · obtain ⟨r,hr,ht⟩ := List.mem_map.mp hz
    subst t
    exact zero_compress R _ _ (fun i hi => htransport i (hP.2.2.2.2.1 r hr i hi))
  · obtain ⟨row,hr,ht⟩ := List.mem_map.mp hl
    subst t
    rw [eval_sum,List.map_map]
    have hmul : ∀ xs : List Op,xs.sum*amplify 17 R.support=(xs.map (fun A => A*amplify 17 R.support)).sum := by
      intro xs
      induction xs with
      | nil => simp
      | cons A xs ih => simp only [List.sum_cons,List.map_cons,add_mul,ih]
    rw [hmul]
    dsimp only
    rw [lift_list_sum]
    congr 1
    simp only [List.map_map,Function.comp_def]
    apply List.map_congr_left
    intro r hr'
    obtain ⟨hp,hq⟩ := hP.2.2.2.2.2 row hr r hr'
    exact linear_term_compress R _ _ _ hp hq

 theorem entry_energy (P : Presentation) (hP : P.admissible) (R : StructuralRealization P)
    (t : Entry) (ht : t∈entries P R) :
    (trace ((scaffoldDensity R.density).op*
      (star (evalPoly (dictionary R) t.1)*evalPoly (dictionary R) t.1))).re=
      (cornerWeight t.2.2.1:ℝ)*(trace (R.density.op*(star t.2.2.2*t.2.2.2))).re := by
  have hs := scaffold_support R.density R.support
    ⟨R.support_projection,R.density_supported,R.faithful_on⟩
  have hc := compress_energy (scaffoldDensity R.density) (amplify 17 R.support)
    (evalPoly (dictionary R) t.1) hs.1 hs.2.1
  rw [← hc,entry_compress P hP R t ht]
  change (trace (weightedOp 17 _ R.density.op*
    (star (matrixOp 17 (singleBlocks 17 t.2.1 t.2.2.1 t.2.2.2))*
      matrixOp 17 (singleBlocks 17 t.2.1 t.2.2.1 t.2.2.2)))).re=_
  rw [single_residual_energy]
  simp [Complex.mul_re]

#print axioms entries_polynomials
#print axioms entries_residuals
#print axioms entry_compress
#print axioms entry_energy
end Sigma2.CompilerApproxMatching
