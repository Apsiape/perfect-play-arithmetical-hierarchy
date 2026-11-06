import Sigma2.CompilerSoundnessJoints
import Sigma2.CompilerSoundnessExtraction

/-! The encoded seventeen-corner cover, from its original polynomial row. -/
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessCover
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessFrame CompilerSoundnessGraphs CompilerSoundnessParameters
  CompilerSoundnessJoints CompilerSoundnessExtraction Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
  CompilerScaffold.polynomialRow CompilerSoundnessGraphs.graphBlock

def graphPolynomial (F : ProjectionName → Op) (p : Poly) : Op :=
  (p.map (fun t => (t.1:ℂ) • graphBlock F t.2 0)).sum

theorem polynomial_row_eval (e : Op) (F : ProjectionName → Op) (p : Poly) :
    evalRow e F (polynomialRow p)=
      (p.map (fun t => (t.1:ℂ) •
        ((2:ℂ) • F (.graph t.2 0 0)-(F (.frame 0)+F (.frame 1))))).sum := by
  induction p with
  | nil => simp [polynomialRow,evalRow,row] <;> module
  | cons t p ih =>
    have hrec : evalRow e F (polynomialRow (t::p))=
        ((2*t.1:ℚ):ℂ) • F (.graph t.2 0 0)+evalRow e F (polynomialRow p)-
          (t.1:ℂ) • F (.frame 0)-(t.1:ℂ) • F (.frame 1) := by
      simp only [polynomialRow,evalRow,row,List.map_cons,List.sum_cons,List.map_append,
        List.sum_append,List.map_map,List.map_nil,List.sum_nil,Rat.cast_add,Rat.cast_neg,
        Rat.cast_zero,zero_smul,zero_add,add_zero,add_smul,neg_smul]
      module
    rw [hrec,ih]
    simp only [List.map_cons,List.sum_cons,Rat.cast_mul,Rat.cast_ofNat]
    module

theorem polynomial_row_compression (e : Op) (F : ProjectionName → Op) (p : Poly) :
    F (.frame 0)*evalRow e F (polynomialRow p)*F (.frame 1)=graphPolynomial F p := by
  rw [polynomial_row_eval]
  induction p with
  | nil => simp [graphPolynomial]
  | cons t p ih =>
    simp only [graphPolynomial,List.map_cons,List.sum_cons] at ih ⊢
    rw [mul_add,add_mul,mul_smul_comm,smul_mul_assoc,ih]
    congr 1
    simp only [graphBlock,pairs,List.getElem?_cons_zero,Option.getD_some]

theorem polynomialRow_mem (P : Presentation) (p : Poly) (hp : p ∈ polynomials P) :
    polynomialRow p ∈ rowList P := by
  simp only [rowList,List.mem_append]
  right
  exact List.mem_map.mpr ⟨p,hp,rfl⟩

def coverPolynomial : Poly := sub (sum ((List.range 17).map corner)) one

theorem coverPolynomial_mem (P : Presentation) : coverPolynomial ∈ polynomials P := by
  simp only [polynomials,List.mem_append]
  left
  simp only [structuralPolynomials,List.mem_append]
  left; left; left; left; left; left
  exact List.mem_cons_self ..

theorem graph_cover_equation (P : Presentation) (e : Op) (F : ProjectionName → Op)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0) :
    (∑ i : Fin 17,graphBlock F [(i.val,false)] 0)+
      (15:ℂ) • graphBlock F [] 0=0 := by
  have hh := congrArg (fun X : Op => F (.frame 0)*X*F (.frame 1))
    (hrows (polynomialRow coverPolynomial) (polynomialRow_mem P coverPolynomial (coverPolynomial_mem P)))
  rw [polynomial_row_compression, mul_zero,zero_mul] at hh
  have heq : (∑ i : Fin 17,graphBlock F [(i.val,false)] 0)+
      (15:ℂ) • graphBlock F [] 0=(2:ℂ) • graphPolynomial F coverPolynomial := by
    norm_num [graphPolynomial,coverPolynomial,CompilerScaffold.sub,CompilerScaffold.sum,
      scale,corner,one,atom,List.range_succ,Fin.sum_univ_succ]
    module
  rw [heq,hh,smul_zero]

theorem projectionA_supported (P : Presentation) (S : NormalStrategy (scenario P))
    (e : Op) (he : Projection e) (n : ProjectionName) :
    e*projectionA P S e n=projectionA P S e n ∧
      projectionA P S e n*e=projectionA P S e n := by
  unfold projectionA
  split_ifs
  · constructor
    · rw [← mul_assoc,← mul_assoc,he.2]
    · rw [mul_assoc,mul_assoc,he.2]
      exact (mul_assoc _ _ _).symm
  · simp

theorem graph_supported (e : Op) (F : ProjectionName → Op)
    (hp : ∀ n,Projection (F n))
    (hs : ∀ n,e*F n=F n ∧ F n*e=F n) (w : Word) (k : ℕ) :
    e*graphBlock F w k=graphBlock F w k ∧ graphBlock F w k*e=graphBlock F w k := by
  let ij := pairs[k]?.getD (0,1)
  constructor
  all_goals unfold graphBlock
  · rw [← mul_assoc,← mul_assoc,(hs _).1]
  · rw [mul_assoc,mul_assoc,(hs _).2]
    exact (mul_assoc _ _ _).symm

theorem propagate_zero (X f u g : Op) (hX : star X=X) (hc : Commute X u)
    (hz : X*f=0) (hl : f*u=u) (hr : star u*u=g) : X*g=0 := by
  have hu : X*u=0 := by
    calc
      _=X*(f*u) := by rw [hl]
      _=0 := by rw [← mul_assoc,hz,zero_mul]
  have hs : star u*X=X*star u := by
    simpa only [star_mul,hX] using congrArg (fun A : Op => star A) hc.eq
  rw [← hr,← mul_assoc,← hs,mul_assoc,hu,mul_zero]

/-- Exact K2 cover, proved from the frozen structural and joint rows. -/
theorem encoded_cover (P : Presentation) (e : Op) (he : Projection e)
    (F : ProjectionName → Op) (hp : ∀ n,Projection (F n))
    (hs : ∀ n,e*F n=F n ∧ F n*e=F n)
    (hframe : ∀ i j : Fin 3,F (.frame i.val)*F (.frame j.val)=
      if i=j then F (.frame j.val) else 0)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0) :
    (∑ i : Fin 17,F (.parameter i.val))=e := by
  let M := ∑ i : Fin 17,F (.parameter i.val)
  let X := M-e
  let g := graphBlock F [] 0
  have hparam (i : Fin 17) := parameter_graph P e F hp hframe hrows
    (⟨i.val,by have := i.isLt; omega⟩ : Fin 25)
  have hsum : (∑ i : Fin 17,graphBlock F [(i.val,false)] 0)=
      (2:ℂ) • (M*g)-(17:ℂ) • g := by
    have hb (i : Fin 17) : graphBlock F [(i.val,false)] 0=
        (2:ℂ) • (F (.parameter i.val)*g)-g := (hparam i 0).2.1
    rw [Finset.sum_congr rfl (fun i _ => hb i)]
    rw [Finset.sum_sub_distrib,← Finset.smul_sum,← Finset.sum_mul]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
    module
  have hxg : X*g=0 := by
    have htwo : (2:ℂ) • (X*g)=0 := by
      calc
        _=(∑ i : Fin 17,graphBlock F [(i.val,false)] 0)+(15:ℂ) • graphBlock F [] 0 := by
          rw [hsum]
          dsimp [X]
          rw [sub_mul,(graph_supported e F hp hs [] 0).1]
          module
        _=0 := graph_cover_equation P e F hrows
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hX : star X=X := by
    change star (M-e)=M-e
    rw [star_sub M e,he.1]
    congr 1
    dsimp [M]
    rw [CompilerAlgebra.op_star_sum]
    exact Finset.sum_congr rfl (fun i _ => (hp _).1)
  have hxcomm (k : Fin 3) : Commute X (graphBlock F [] k.val) := by
    have hM : Commute M (graphBlock F [] k.val) := by
      change (∑ i : Fin 17,F (.parameter i.val))*_= _*(∑ i : Fin 17,F (.parameter i.val))
      rw [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => (hparam i k).2.2.eq)
    have hsG := graph_supported e F hp hs [] k.val
    exact hM.sub_left (hsG.1.trans hsG.2.symm)
  have hiso (k : Fin 3) :
      star (graphBlock F [] k.val)*graphBlock F [] k.val=F (.frame (pairs[k.val]?.getD (0,1)).2) ∧
      graphBlock F [] k.val*star (graphBlock F [] k.val)=F (.frame (pairs[k.val]?.getD (0,1)).1) := by
    apply graph_isometry e F hp [] k.val (fun r hr => hrows r (graphRow_mem P [] (empty_mem_words P) k r hr))
    exact (hframe ⟨_,(pair_bounds k).1⟩ ⟨_,(pair_bounds k).2.1⟩).trans
      (if_neg (by intro h; exact (pair_bounds k).2.2 (congrArg Fin.val h)))
  have hz0 : X*F (.frame 0)=0 := by
    calc
      _=X*(g*star g) := by
        have hi : g*star g=F (.frame 0) := by simpa [g,pairs] using (hiso 0).2
        rw [hi]
      _=0 := by rw [← mul_assoc,hxg,zero_mul]
  have hleft (k : Fin 2) : F (.frame 0)*graphBlock F [] k.val=graphBlock F [] k.val := by
    fin_cases k <;> simp only [graphBlock,pairs,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some] <;>
      rw [← mul_assoc,← mul_assoc,(hp (.frame 0)).2]
  have hz (i : Fin 3) : X*F (.frame i.val)=0 := by
    fin_cases i
    · exact hz0
    · exact propagate_zero X (F (.frame 0)) (graphBlock F [] 0) (F (.frame 1))
        hX (hxcomm 0) hz0 (hleft 0) (hiso 0).1
    · exact propagate_zero X (F (.frame 0)) (graphBlock F [] 1) (F (.frame 2))
        hX (hxcomm 1) hz0 (hleft 1) (hiso 1).1
  have hXe : X*e=X := by
    dsimp [X,M]
    rw [sub_mul,he.2,Finset.sum_mul]
    simp_rw [fun i : Fin 17 => (hs (.parameter i.val)).2]
  have hzero : X=0 := by
    rw [← hXe,← frame_sum P e F hrows,Finset.mul_sum]
    exact Finset.sum_eq_zero (fun i _ => hz i)
  exact sub_eq_zero.mp hzero

theorem actual_cover (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e)
    (hrows : ∀ r ∈ rowList P,evalRow e (projectionA P S e) r=0) :
    (∑ i : Fin 17,projectionA P S e (.parameter i.val))=e :=
  encoded_cover P e he.1 (projectionA P S e) (CompilerSoundnessNames.sharpA P S hS h hm e he)
    (projectionA_supported P S e he.1) (actual_frame P S hS h hm e he hrows).2.1 hrows

theorem actual_source_mass (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e)
    (hrows : ∀ r ∈ rowList P,evalRow e (projectionA P S e) r=0) :
    (trace (h.op*projectionA P S e (.parameter 0))).re=1/121 :=
  named_source_mass_of_cover P S hS h hm e he (actual_cover P S hS h hm e he hrows)

theorem supported_source_mass {P : Presentation} (E : SupportedScaffold P) :
    (trace (E.densityA.op*projectionA P E.strategy E.supportA (.parameter 0))).re=1/121 :=
  actual_source_mass P E.strategy E.perfect E.densityA E.marginalA E.supportA E.supportA_laws E.rowsA

#print axioms encoded_cover
#print axioms actual_cover
#print axioms actual_source_mass
#print axioms supported_source_mass
end Sigma2.CompilerSoundnessCover
