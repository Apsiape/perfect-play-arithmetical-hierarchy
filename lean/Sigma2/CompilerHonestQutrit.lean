import Sigma2.CompilerScaffoldAlgebra
import Sigma2.FiniteAncillaMatrix

/-! Explicit honest qutrit graph and triangle projections at the frozen rational
3-4-5 interface. No application equations are hypotheses of the graph construction. -/
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerHonestQutrit
open CompilerScaffold

/-- The first two scalar frame projections as one matrix. -/
def pairFrame : Matrix (Fin 3) (Fin 3) Op :=
  !![1,0,0;0,1,0;0,0,0]

/-- The unitary graph in the first qutrit pair. -/
def graphBlocks (U : Op) : Matrix (Fin 3) (Fin 3) Op :=
  !![(1/2:ℂ) • (1:Op),(1/2:ℂ) • U,0;
     (1/2:ℂ) • star U,(1/2:ℂ) • (1:Op),0;
     0,0,0]

/-- Its calibrated rational 3-4-5 companion. -/
def calibratedBlocks (U : Op) : Matrix (Fin 3) (Fin 3) Op :=
  !![(4/5:ℂ) • (1:Op),(2/5:ℂ) • U,0;
     (2/5:ℂ) • star U,(1/5:ℂ) • (1:Op),0;
     0,0,0]

theorem graphBlocks_projective (U : Op) (hU : Unitary U) :
    star (graphBlocks U)=graphBlocks U ∧ graphBlocks U*graphBlocks U=graphBlocks U := by
  constructor
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [graphBlocks,Matrix.star_apply,star_zero Op]
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [graphBlocks,Matrix.mul_apply,Fin.sum_univ_three,
        smul_mul_smul_comm,hU.1,hU.2] <;> module

theorem calibratedBlocks_projective (U : Op) (hU : Unitary U) :
    star (calibratedBlocks U)=calibratedBlocks U ∧
      calibratedBlocks U*calibratedBlocks U=calibratedBlocks U := by
  constructor
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [calibratedBlocks,Matrix.star_apply,star_zero Op]
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [calibratedBlocks,Matrix.mul_apply,Fin.sum_univ_three,
        smul_mul_smul_comm,hU.1,hU.2] <;> module

/-- The frozen 3-4-5 row holds at the actual operator-valued matrix level. -/
theorem calibrated_row (U : Op) :
    (5:ℂ) • calibratedBlocks U+
      (!![(1:Op),0,0;0,0,0;0,0,0] : Matrix (Fin 3) (Fin 3) Op)+
      (!![(0:Op),0,0;0,1,0;0,0,0] : Matrix (Fin 3) (Fin 3) Op)=
    (3:ℂ) • (!![(1:Op),0,0;0,0,0;0,0,0] : Matrix (Fin 3) (Fin 3) Op)+
      (4:ℂ) • graphBlocks U := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [calibratedBlocks,graphBlocks,Matrix.add_apply,Matrix.smul_apply] <;> module

/-- Word evaluation is unitary for one common honest unitary dictionary. -/
theorem evalWord_unitary (U : ℕ → Op) (hU : ∀ i,Unitary (U i)) (w : Word) :
    Unitary (evalWord U w) := by
  induction w with
  | nil => simp [evalWord,Unitary]
  | cons t w ih =>
    have ht : Unitary (if t.2 then star (U t.1) else U t.1) := by
      split_ifs
      · exact ⟨by simpa using (hU t.1).2,by simpa using (hU t.1).1⟩
      · exact hU t.1
    change Unitary ((if t.2 then star (U t.1) else U t.1)*evalWord U w)
    constructor
    · rw [star_mul,mul_assoc,← mul_assoc _ _ (evalWord U w),ht.1,one_mul,ih.1]
    · rw [star_mul,← mul_assoc,mul_assoc _ (evalWord U w),ih.2,mul_one,ht.2]

/-- The product triangle is an honest projection, with the actual product in
its 02 block, so all prefix and inverse triangles can use the same dictionary. -/
def triangleBlocks (U V W : Op) : Matrix (Fin 3) (Fin 3) Op :=
  !![(1/3:ℂ) • (1:Op),(1/3:ℂ) • U,(1/3:ℂ) • W;
     (1/3:ℂ) • star U,(1/3:ℂ) • (1:Op),(1/3:ℂ) • V;
     (1/3:ℂ) • star W,(1/3:ℂ) • star V,(1/3:ℂ) • (1:Op)]

theorem triangleBlocks_projective (U V W : Op) (hU : Unitary U) (hV : Unitary V)
    (hW : W=U*V) :
    star (triangleBlocks U V W)=triangleBlocks U V W ∧
      triangleBlocks U V W*triangleBlocks U V W=triangleBlocks U V W := by
  have hWl : star W*W=1 := by
    rw [hW,star_mul,mul_assoc,← mul_assoc (star U) U V,hU.1,one_mul,hV.1]
  have hWr : W*star W=1 := by
    rw [hW,star_mul,← mul_assoc,mul_assoc U V (star V),hV.2,mul_one,hU.2]
  have hWU : W*star V=U := by rw [hW,mul_assoc,hV.2,mul_one]
  have hUV : star U*W=V := by rw [hW,← mul_assoc,hU.1,one_mul]
  have hVW : V*star W=star U := by rw [hW,star_mul,← mul_assoc,hV.2,one_mul]
  have hUW : star W*U=star V := by rw [hW,star_mul,mul_assoc,hU.1,mul_one]
  have hstarW : star V*star U=star W := by rw [hW,star_mul]
  constructor
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [triangleBlocks,Matrix.star_apply,star_zero Op]
  · apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [triangleBlocks,Matrix.mul_apply,Fin.sum_univ_three,
        smul_mul_smul_comm,hU.1,hU.2,hV.1,hV.2,hWl,hWr,hWU,hUV,hVW,hUW,hstarW,← hW]
    all_goals module

/-- These are genuine bounded projections on the project's fixed l2 space. -/
theorem graph_projection (U : Op) (hU : Unitary U) :
    Projection (FiniteAncilla.matrixOp 3 (graphBlocks U)) := by
  have hp := graphBlocks_projective U hU
  exact FiniteAncilla.matrixOp_projection 3 _ hp.1 hp.2

theorem calibrated_projection (U : Op) (hU : Unitary U) :
    Projection (FiniteAncilla.matrixOp 3 (calibratedBlocks U)) := by
  have hp := calibratedBlocks_projective U hU
  exact FiniteAncilla.matrixOp_projection 3 _ hp.1 hp.2

theorem triangle_projection (U V W : Op) (hU : Unitary U) (hV : Unitary V)
    (hW : W=U*V) : Projection (FiniteAncilla.matrixOp 3 (triangleBlocks U V W)) := by
  have hp := triangleBlocks_projective U V W hU hV hW
  exact FiniteAncilla.matrixOp_projection 3 _ hp.1 hp.2

#print axioms graph_projection
#print axioms calibrated_projection
#print axioms triangle_projection
#print axioms evalWord_unitary
end Sigma2.CompilerHonestQutrit
