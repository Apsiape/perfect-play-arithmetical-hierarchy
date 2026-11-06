import Sigma2.CompilerApproxRows
import Sigma2.CompilerHonestStrategy

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerRegisterIdentities
open Compiler CompilerScaffold CompilerHonestDictionary CompilerFiniteRegister
  CompilerHonestLift CompilerHonestSyntax CompilerApproxDictionary
  CompilerApproxResidual CompilerApproxBlocks FiniteAncilla RowCompleteness

theorem list_sum_range {α : Type} [AddCommMonoid α] (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).sum=∑ i : Fin n,f i.val := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa [List.range_succ,List.map_append,List.sum_append,Fin.sum_univ_castSucc] using (congrArg (fun a => a+f n) ih)

theorem eval_sum_range (U : ℕ → Op) (f : ℕ → Poly) (n : ℕ) :
    evalPoly U (CompilerScaffold.sum ((List.range n).map f))=∑ i : Fin n,evalPoly U (f i.val) := by
  rw [eval_sum,List.map_map,list_sum_range]
  rfl

theorem eval_parameter {P : Presentation} (R : StructuralRealization P) (n : ℕ) (hn : n<25) :
    evalPoly (dictionary R) (CompilerScaffold.corner n)=parameter n := by
  rw [eval_corner]
  have he : dictionary R n=reflection (parameter n) := by simp only [dictionary,dif_pos hn]
  rw [he,reflection]
  module

theorem diagonal_add (d : ℕ) [NeZero d] (A B : Fin d → Op) :
    diagonal d (fun i => A i+B i)=diagonal d A+diagonal d B := by
  unfold diagonal
  rw [← matrixOp_add,← Matrix.diagonal_add]

theorem diagonal_smul (d : ℕ) [NeZero d] (c : ℂ) (A : Fin d → Op) :
    diagonal d (fun i => c • A i)=c • diagonal d A := by
  unfold diagonal
  rw [← matrixOp_smul]
  congr 1
  ext i j
  by_cases hi : i=j <;> simp [Matrix.diagonal_apply,hi]

def diagLinear (d : ℕ) [NeZero d] : (Fin d → Op) →ₗ[ℂ] Op where
  toFun := diagonal d
  map_add' := diagonal_add d
  map_smul' := diagonal_smul d

theorem diagonal_sub (d : ℕ) [NeZero d] (A B : Fin d → Op) :
    diagonal d (fun i => A i-B i)=diagonal d A-diagonal d B :=
  map_sub (diagLinear d) A B

theorem conjugate_diagonal (d : ℕ) [NeZero d] (e : Equiv.Perm (Fin d)) (A : Fin d → Op) :
    permutation d e*diagonal d A*star (permutation d e)=diagonal d (fun i => A (e i)) := by
  rw [permutation,diagonal,← matrixOp_star,permutation_star,← matrixOp_mul,← matrixOp_mul]
  congr 1
  ext i j
  rw [permutation_right,permutation_left]
  simp [Matrix.diagonal_apply,e.injective.eq_iff]

theorem corner_copy_diagonal (d : ℕ) [NeZero d] (a : Fin d) (U : Op) :
    CompilerFiniteRegister.corner d a*copy d a U=diagonal d (fun i => if i=a then U else 0) := by
  rw [CompilerFiniteRegister.corner,copy,diagonal_mul]
  congr 1
  funext i
  split_ifs <;> simp

theorem magic_sum (g : Fin 4) :
    (∑ k : Fin 4,CompilerFiniteRegister.corner 17 (magicIndex g k))=mask 17 (magicActive g) := by
  change (∑ k : Fin 4,diagLinear 17 (fun i => if i=magicIndex g k then (1:Op) else 0))=_
  rw [← map_sum]
  change diagonal 17 _=diagonal 17 _
  congr 1
  funext i
  simp only [Finset.sum_apply,Fin.sum_univ_succ,Fin.sum_univ_zero]
  fin_cases g <;> fin_cases i <;> norm_num [magicIndex,magicActive]

theorem activity_sum (g : Fin 4) :
    CompilerFiniteRegister.corner 17 (selected g.val)+mask 17 (magicActive g)=mask 17 (bridgeActive g.val) := by
  rw [CompilerFiniteRegister.corner,mask,← diagonal_add]
  change diagonal 17 _=diagonal 17 _
  congr 1
  funext i
  fin_cases g <;> fin_cases i <;> norm_num [magicActive,bridgeActive,selected,cornerIndex]

theorem eval_magic {P : Presentation} (R : StructuralRealization P) (g : Fin 4) :
    evalPoly (dictionary R) (magic g.val)=mask 17 (magicActive g) := by
  rw [magic,eval_sum_range]
  rw [← magic_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [eval_parameter R _ (by have := g.isLt; have := k.isLt; omega)]
  simp only [parameter,dif_pos (show 1+4*g.val+k.val<17 by have := g.isLt; have := k.isLt; omega)]
  rfl

theorem eval_activity {P : Presentation} (R : StructuralRealization P) (g : Fin 4) :
    evalPoly (dictionary R) (activity g.val)=mask 17 (bridgeActive g.val) := by
  rw [activity,evalPoly_append,eval_e R _ (by have := g.isLt; omega),eval_magic,activity_sum]

theorem eval_axis {P : Presentation} (R : StructuralRealization P) (g : Fin 4) (k : Fin 2) :
    evalPoly (dictionary R) (axis g.val k.val)=axisUnitary g k := by
  rw [axis,eval_atom]
  have hg := g.isLt
  have hk := k.isLt
  simp only [dictionary]
  rw [dif_neg (by omega),dif_pos (by omega)]
  have he : 25+2*g.val+k.val-25=2*g.val+k.val := by omega
  simp only [he,show (2*g.val+k.val)/2=g.val by omega,show (2*g.val+k.val)%2=k.val by omega,Fin.eta]

theorem eval_axis_parameter {P : Presentation} (R : StructuralRealization P) (g : Fin 4) (k : Fin 2) :
    evalPoly (dictionary R) (axisParameter g.val k.val)=positiveAxis g k := by
  rw [axisParameter,eval_parameter R _ (by have := g.isLt; have := k.isLt; omega)]
  have hg := g.isLt
  have hk := k.isLt
  simp only [parameter]
  rw [dif_neg (by omega),dif_pos (by omega)]
  have he : 17+2*g.val+k.val-17=2*g.val+k.val := by omega
  simp only [he,show (2*g.val+k.val)/2=g.val by omega,show (2*g.val+k.val)%2=k.val by omega,Fin.eta]

theorem matrixOp_sub_any (d : ℕ) [NeZero d] (A B : Matrix (Fin d) (Fin d) Op) :
    matrixOp d (A-B)=matrixOp d A-matrixOp d B := by
  have hn : matrixOp d (-B)= -matrixOp d B := by
    simpa only [neg_one_smul ℂ B,neg_one_smul ℂ (matrixOp d B)] using (matrixOp_smul d (-1:ℂ) B)
  simp only [sub_eq_add_neg,matrixOp_add,hn]

theorem axis_fixed_outside : ∀ (g : Fin 4) (k : Fin 2) (i : Fin 17),
    magicActive g i≠true → axisPerm g k i=i := by decide

theorem axis_outside (g : Fin 4) (k : Fin 2) :
    axisUnitary g k=1-mask 17 (magicActive g)+mask 17 (magicActive g)*axisUnitary g k := by
  change matrixOp 17 (permutationMatrix (axisPerm g k))=_
  rw [← matrixOp_one 17]
  change matrixOp 17 _=matrixOp 17 (1:Matrix (Fin 17) (Fin 17) Op)-
    matrixOp 17 (Matrix.diagonal _)+matrixOp 17 (Matrix.diagonal _)*matrixOp 17 _
  rw [← matrixOp_sub_any,← matrixOp_mul,← matrixOp_add]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [Matrix.add_apply,Matrix.sub_apply]
  rw [Matrix.diagonal_mul]
  change (if j=axisPerm g k i then (1:Op) else 0)=
    (if i=j then 1 else 0)-(if i=j then (if magicActive g i then 1 else 0) else 0)+
      (if magicActive g i then 1 else 0)*(if j=axisPerm g k i then 1 else 0)
  by_cases hi : magicActive g i=true
  · by_cases hij : i=j
    · subst j
      simp [hi]
    · simp [hi,hij]
  · have he := axis_fixed_outside g k i hi
    rw [he]
    by_cases hij : i=j
    · subst j
      simp [hi]
    · simp [hi,hij,Ne.symm hij]

#print axioms eval_magic
#print axioms eval_activity
#print axioms axis_outside
end Sigma2.CompilerRegisterIdentities
