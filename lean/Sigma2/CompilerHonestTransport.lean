import Sigma2.CompilerRegisterIdentities

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestTransport
open Compiler CompilerScaffold CompilerHonestDictionary CompilerFiniteRegister
  CompilerHonestLift CompilerHonestSyntax CompilerApproxDictionary
  CompilerApproxResidual CompilerRegisterIdentities FiniteAncilla RowCompleteness

def axes (g : Fin 4) (k : ℕ) : Op :=
  (if k/2=0 then 1 else axisUnitary g 0)*(if k%2=0 then 1 else axisUnitary g 1)

theorem axes_transport (g : Fin 4) (k : Fin 4) (U : Op) :
    axes g k.val*(CompilerFiniteRegister.corner 17 (selected (g.val+1))*
      copy 17 (selected (g.val+1)) U)*star (axes g k.val)=
      diagonal 17 (fun i => if i=magicIndex g k then U else 0) := by
  have hs : selected (g.val+1)=magicIndex g 0 := by
    apply Fin.ext
    simp [selected,show g.val+1<5 by have := g.isLt; omega,cornerIndex,magicIndex]
  rw [corner_copy_diagonal,hs]
  fin_cases k
  · simp [axes]
  · simp only [axes,show (1:ℕ)/2=0 by decide,show (1:ℕ)%2=1 by decide,
      ite_true,if_neg (show (1:ℕ)≠0 by decide),one_mul,axisUnitary]
    rw [conjugate_diagonal]
    congr 1
    funext i
    have he : (axisPerm g 1 i=magicIndex g 0) ↔ i=magicIndex g 1 := by
      fin_cases g <;> fin_cases i <;> norm_num [axisPerm,magicIndex,Equiv.swap_apply_def]
    simp only [he] <;> norm_num [magicIndex]
  · simp only [axes,show (2:ℕ)/2=1 by decide,show (2:ℕ)%2=0 by decide,
      ite_true,if_neg (show (1:ℕ)≠0 by decide),mul_one,axisUnitary]
    rw [conjugate_diagonal]
    congr 1
    funext i
    have he : (axisPerm g 0 i=magicIndex g 0) ↔ i=magicIndex g 2 := by
      fin_cases g <;> fin_cases i <;> norm_num [axisPerm,magicIndex,Equiv.swap_apply_def]
    simp only [he] <;> norm_num [magicIndex]
  · simp only [axes,show (3:ℕ)/2=1 by decide,show (3:ℕ)%2=1 by decide,
      if_neg (show (1:ℕ)≠0 by decide),axisUnitary]
    rw [star_mul (permutation 17 (axisPerm g 0)) (permutation 17 (axisPerm g 1))]
    calc
      _=permutation 17 (axisPerm g 0)*(permutation 17 (axisPerm g 1)*
        diagonal 17 (fun i => if i=magicIndex g 0 then U else 0)*
          star (permutation 17 (axisPerm g 1)))*star (permutation 17 (axisPerm g 0)) := by noncomm_ring
      _=diagonal 17 (fun i => if i=magicIndex g 3 then U else 0) := by
        rw [conjugate_diagonal,conjugate_diagonal]
        congr 1
        funext i
        have he : (axisPerm g 1 (axisPerm g 0 i)=magicIndex g 0) ↔ i=magicIndex g 3 := by
          fin_cases g <;> fin_cases i <;> norm_num [axisPerm,magicIndex,Equiv.swap_apply_def]
        simp only [he] <;> norm_num [magicIndex]

theorem eval_transport {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (l : Fin (encodingCount P)) (k : Fin 4) :
    evalPoly (dictionary R) (transportTerm P g.val l.val k.val)=
      diagonal 17 (fun i => if i=magicIndex g k then encoding R l.val else 0) := by
  have h0 : evalPoly (dictionary R) (axis g.val 0)=axisUnitary g 0 := by
    simpa using (eval_axis R g (0 : Fin 2))
  have h1 : evalPoly (dictionary R) (axis g.val 1)=axisUnitary g 1 := by
    simpa using (eval_axis R g (1 : Fin 2))
  have he : evalPoly (dictionary R) (if k.val/2=0 then CompilerScaffold.one else axis g.val 0)*
      evalPoly (dictionary R) (if k.val%2=0 then CompilerScaffold.one else axis g.val 1)=axes g k.val := by
    split_ifs <;> simp_all only [eval_one,h0,h1,axes,ite_true,ite_false]
  simp only [transportTerm,evalPoly_mul,eval_adj]
  simp only [he]
  rw [eval_e R _ (by have := g.isLt; omega),copyAtom,eval_atom,
    dictionary_copy R _ _ (by have := g.isLt; omega) l.isLt]
  exact axes_transport g k (encoding R l.val)

theorem block_identity (g : Fin 4) (U : Op) :
    repeated 17 (bridgeActive g.val) U=
      1-mask 17 (bridgeActive g.val)+
        CompilerFiniteRegister.corner 17 (selected g.val)*copy 17 (selected g.val) U+
          ∑ k : Fin 4,diagonal 17 (fun i => if i=magicIndex g k then U else 0) := by
  rw [corner_copy_diagonal]
  have ht : diagonal 17 (∑ k : Fin 4,(fun i => if i=magicIndex g k then U else 0))=
      ∑ k : Fin 4,diagonal 17 (fun i => if i=magicIndex g k then U else 0) :=
    map_sum (diagLinear 17) _ _
  rw [← ht,← diagonal_one 17]
  change diagonal 17 _=diagonal 17 _-diagonal 17 _+diagonal 17 _+diagonal 17 _
  rw [← diagonal_sub,← diagonal_add,← diagonal_add]
  congr 1
  funext i
  simp only [Finset.sum_apply,Fin.sum_univ_succ,Fin.sum_univ_zero]
  fin_cases g <;> fin_cases i <;>
    norm_num [bridgeActive,selected,cornerIndex,magicIndex] <;> module

theorem eval_block_equation {P : Presentation} (R : StructuralRealization P)
    (g : Fin 4) (l : Fin (encodingCount P)) :
    evalPoly (dictionary R) (CompilerScaffold.sub (blockAtom P g.val l.val)
      (CompilerScaffold.sub CompilerScaffold.one (activity g.val) ++
        CompilerScaffold.mul (e g.val) (copyAtom P g.val l.val) ++
          CompilerScaffold.sum ((List.range 4).map (transportTerm P g.val l.val))))=0 := by
  have hb : evalPoly (dictionary R) (blockAtom P g.val l.val)=
      repeated 17 (bridgeActive g.val) (encoding R l.val) := by
    simpa [blockAtom,eval_atom,evalWord] using CompilerHonestCommute.eval_block R g l
  rw [evalPoly_sub,hb,evalPoly_append,evalPoly_append,evalPoly_sub,eval_one,eval_activity,
    evalPoly_mul,eval_e R _ (by have := g.isLt; omega),copyAtom,eval_atom,
    dictionary_copy R _ _ (by have := g.isLt; omega) l.isLt,eval_sum_range]
  have ht : (∑ k : Fin 4,evalPoly (dictionary R) (transportTerm P g.val l.val k.val))=
      ∑ k : Fin 4,diagonal 17 (fun i => if i=magicIndex g k then encoding R l.val else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact eval_transport R g l k
  rw [ht]
  exact sub_eq_zero.mpr (block_identity g (encoding R l.val))

#print axioms axes_transport
#print axioms eval_transport
#print axioms eval_block_equation
end Sigma2.CompilerHonestTransport
