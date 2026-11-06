import Sigma2.CompilerSoundnessBindings

/-! Decode the actual rational RowGame equations. Coefficient aggregation is
proved for the finite event dictionary, including repeated row occurrences. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessRows
open Compiler CompilerScaffold CompilerSoundnessNames Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

def evalRow (e : Op) (F : ProjectionName → Op) (r : RationalRow) : Op :=
  (r.constant:ℂ) • e+(r.terms.map (fun t => (t.1:ℂ) • F t.2)).sum

theorem coefficient_cons (c q : ℚ) (n z : ProjectionName) (xs : List (ℚ × ProjectionName)) :
    coefficient (row ((q,n)::xs) c) z=
      (if n=z then q else 0)+coefficient (row xs c) z := by
  by_cases hn : n=z <;> simp [coefficient,row,hn]

theorem dictionary_single (P : Presentation) (F : ProjectionName → Op)
    (q : ℚ) (n : ProjectionName) (hn : n ∈ names P) :
    (∑ i : Fin (names P).length,(((if n=(names P)[i.val] then q else 0):ℚ):ℂ) • F ((names P)[i.val]))=
      (q:ℂ) • F n := by
  rw [Finset.sum_eq_single (nameIndex P n hn)]
  · rw [get_nameIndex,if_pos rfl]
  · intro i _ hi
    have hne : n≠(names P)[i.val] := by
      intro hh
      apply hi
      apply (names_nodup P).get_inj_iff.mp
      exact hh.symm.trans (get_nameIndex P n hn).symm
    simp only [hne,ite_false]
    norm_num
    module
  · intro hh
    exact False.elim (hh (Finset.mem_univ _))

theorem dictionary_sum (P : Presentation) (F : ProjectionName → Op)
    (c : ℚ) (xs : List (ℚ × ProjectionName))
    (hmem : ∀ t ∈ xs,t.2 ∈ names P) :
    (∑ i : Fin (names P).length,(coefficient (row xs c) ((names P)[i.val]):ℂ) • F ((names P)[i.val]))=
      (xs.map (fun t => (t.1:ℂ) • F t.2)).sum := by
  induction xs with
  | nil =>
    simp only [coefficient,row,List.filter_nil,List.map_nil,List.sum_nil]
    apply Finset.sum_eq_zero
    intro i _
    norm_num
    module
  | cons t xs ih =>
    rcases t with ⟨q,n⟩
    have hn := hmem (q,n) (List.mem_cons_self ..)
    have ht : ∀ t ∈ xs,t.2 ∈ names P := fun t h => hmem t (List.mem_cons_of_mem _ h)
    simp only [coefficient_cons,List.map_cons,List.sum_cons]
    calc
      _ = ∑ i : Fin (names P).length,
          ((((if n=(names P)[i.val] then q else 0):ℚ):ℂ) • F ((names P)[i.val])+
          (coefficient (row xs c) ((names P)[i.val]):ℂ) • F ((names P)[i.val])) := by
        apply Finset.sum_congr rfl
        intro i _
        push_cast
        module
      _ = _ := by rw [Finset.sum_add_distrib,dictionary_single P F q n hn,ih ht]

theorem projectionA_index (P : Presentation) (S : NormalStrategy (scenario P))
    (e : Op) (i : Fin (names P).length) :
    projectionA P S e ((names P)[i.val])=e*S.measurements.alice (event P i).x 1*e := by
  have hn : (names P)[i.val] ∈ names P := List.getElem_mem i.isLt
  rw [projectionA_of_mem P S e _ hn]
  have hi : nameIndex P ((names P)[i.val]) hn=i := by
    apply (names_nodup P).get_inj_iff.mp
    exact get_nameIndex P _ hn
  rw [namedEvent,hi]

theorem projectionB_index (P : Presentation) (S : NormalStrategy (scenario P))
    (e : Op) (i : Fin (names P).length) :
    projectionB P S e ((names P)[i.val])=e*S.measurements.bob (event P i).y 1*e := by
  have hn : (names P)[i.val] ∈ names P := List.getElem_mem i.isLt
  rw [projectionB_of_mem P S e _ hn]
  have hi : nameIndex P ((names P)[i.val]) hn=i := by
    apply (names_nodup P).get_inj_iff.mp
    exact get_nameIndex P _ hn
  rw [namedEvent,hi]

/-- Cancellation is only on the actual marginal support. -/
theorem density_support_cancel (h : Density) (e : Op) (he : SupportOf h e)
    (A : Op) (hz : A*h.op=0) : A*e=0 := by
  have hd : h.op*e=h.op := (MatrixCentralizer.support_centralizes h e he).eq.trans he.2.1
  have hzero : star (0:Op)=0 := by rw [ContinuousLinearMap.star_eq_adjoint]; exact map_zero _
  have hs : h.op*star A=0 := by
    have hh := congrArg (fun B : Op => star B) hz
    simpa only [star_mul,h.positive.isSelfAdjoint.star_eq,hzero] using hh
  have hx : e*star A=0 := by
    apply ContinuousLinearMap.ext
    intro v
    apply he.2.2 ((e*star A) v)
    · change (e*(e*star A)) v=(e*star A) v
      rw [← mul_assoc,he.1.2]
    · change (h.op*(e*star A)) v=0
      rw [← mul_assoc,hd,hs]
      rfl
  have hh := congrArg (fun B : Op => star B) hx
  simpa only [star_mul,star_star,he.1.1,hzero] using hh

theorem indexed_row (P : Presentation) (h : Density) (e : Op) (he : SupportOf h e)
    (F : ProjectionName → Op) (E : Fin (names P).length → Op)
    (r : RationalRow) (hr : r ∈ rowList P)
    (hE : ∀ i,e*E i*e=F ((names P)[i.val]))
    (hz : ((r.constant:ℂ) • (1:Op)+∑ i,(coefficient r ((names P)[i.val]):ℂ) • E i)*h.op=0) :
    evalRow e F r=0 := by
  have hh := density_support_cancel h e he _ hz
  have hc := congrArg (fun A : Op => e*A) hh
  rw [← mul_assoc] at hc
  have hs : ((r.terms.map (fun t => (t.1:ℂ) • F t.2)).sum)=
      ∑ i : Fin (names P).length,(coefficient r ((names P)[i.val]):ℂ) • F ((names P)[i.val]) := by
    exact (dictionary_sum P F r.constant r.terms
      (fun t ht => row_name_mem P r hr t.2 (List.mem_map.mpr ⟨t,ht,rfl⟩))).symm
  unfold evalRow
  rw [hs]
  simpa only [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,Finset.mul_sum,Finset.sum_mul,
    one_mul,mul_one,he.1.2,hE,mul_zero] using hc

theorem rows_alice (P : Presentation) (S : NormalStrategy (scenario P))
    (h : Density) (e : Op) (he : SupportOf h e)
    (hrows : ∀ r,(((rows P).constant r:ℂ) • (1:Op)+∑ i,((rows P).coefficient r i:ℂ) •
      S.measurements.alice ((rows P).event i).x ((rows P).event i).a)*h.op=0)
    (r : RationalRow) (hr : r ∈ rowList P) : evalRow e (projectionA P S e) r=0 := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
  apply indexed_row P h e he (projectionA P S e)
    (fun i => S.measurements.alice (event P i).x 1) r hr
    (fun i => (projectionA_index P S e i).symm)
  have hi' : (rowList P)[i.val]=r := hi
  have hh := hrows i
  change (((rowList P)[i.val].constant:ℂ) • (1:Op)+
    ∑ j : Fin (names P).length,(coefficient ((rowList P)[i.val]) ((names P)[j.val]):ℂ) •
      S.measurements.alice (event P j).x 1)*h.op=0 at hh
  rwa [hi'] at hh

theorem rows_bob (P : Presentation) (S : NormalStrategy (scenario P))
    (h : Density) (e : Op) (he : SupportOf h e)
    (hrows : ∀ r,(((rows P).constant r:ℂ) • (1:Op)+∑ i,((rows P).coefficient r i:ℂ) •
      S.measurements.bob ((rows P).event i).y ((rows P).event i).b)*h.op=0)
    (r : RationalRow) (hr : r ∈ rowList P) : evalRow e (projectionB P S e) r=0 := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hr
  apply indexed_row P h e he (projectionB P S e)
    (fun i => S.measurements.bob (event P i).y 1) r hr
    (fun i => (projectionB_index P S e i).symm)
  have hi' : (rowList P)[i.val]=r := hi
  have hh := hrows i
  change (((rowList P)[i.val].constant:ℂ) • (1:Op)+
    ∑ j : Fin (names P).length,(coefficient ((rowList P)[i.val]) ((names P)[j.val]):ℂ) •
      S.measurements.bob (event P j).y 1)*h.op=0 at hh
  rwa [hi'] at hh

theorem decoded_rows (P : Presentation) (S : NormalStrategy (scenario P))
    (hR : RowsHold (rows P) S) :
    ∃ (hA hB : Density) (eA eB : Op),
      MarginalA S hA ∧ MarginalB S hB ∧ SupportOf hA eA ∧ SupportOf hB eB ∧
      (∀ r ∈ rowList P,evalRow eA (projectionA P S eA) r=0) ∧
      (∀ r ∈ rowList P,evalRow eB (projectionB P S eB) r=0) := by
  obtain ⟨hA,hB,hmA,hmB,hmirror,hrowsA,hrowsB⟩ := hR
  obtain ⟨eA,heA⟩ := support_exists hA
  obtain ⟨eB,heB⟩ := support_exists hB
  exact ⟨hA,hB,eA,eB,hmA,hmB,heA,heB,rows_alice P S hA eA heA hrowsA,
    rows_bob P S hB eB heB hrowsB⟩

#print axioms dictionary_sum
#print axioms density_support_cancel
#print axioms indexed_row
#print axioms decoded_rows
end Sigma2.CompilerSoundnessRows
