import Sigma2.DiagonalIdentification
import Sigma2.MatrixCentralizer
noncomputable section
open scoped BigOperators InnerProductSpace ENNReal
namespace Sigma2.BridgeMatrixUnits
open Compiler TensorLifts PureSupport Preliminaries Coefficients CoarseCells FiniteSpectral MagicCells MagicRelations MirrorAlgebra PauliMatrixUnits FourUnits DiagonalIdentification MatrixCentralizer

def index (i : Fin 4) : Index := (⟨i.val/2,by omega⟩,⟨i.val%2,by omega⟩)

theorem index_injective : Function.Injective index := by
  intro i j hij
  have h1 := congrArg (fun z : Index => z.1.val) hij
  have h2 := congrArg (fun z : Index => z.2.val) hij
  apply Fin.ext
  dsimp [index] at h1 h2
  omega

def actualUnit {s} (S : PureStrategy s) (I : FMSInstance s) (P : Op) (i j : Fin 4) : Op :=
  matrixUnit (rowActive S I P 0) (rowCell S I P 1 1) (rowCell S I P 0 0)
    (rowCell S I P 0 1) (rowCell S I P 1 0) (index i) (index j)

theorem units_analysis {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    (∀ i j k l,actualUnit S I P i j*actualUnit S I P k l=if j=k then actualUnit S I P i l else 0) ∧
    (∀ i j,star (actualUnit S I P i j)=actualUnit S I P j i) ∧
    (∀ i,actualUnit S I P i i=P*magicA (normalOfPure S) I i*P) ∧
    (∀ i j,Centralizes h.op (actualUnit S I P i j)) ∧
    (∑ i,actualUnit S I P i i)=rowActive S I P 0 := by
  obtain ⟨hprod,hstar,hsum⟩ := actual_matrix_units S I hS h hm P hP
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i j k l
    have hh := hprod (index i) (index j) (index k) (index l)
    by_cases hjk : j=k
    · simpa only [actualUnit,hjk,ite_true] using hh
    · have hi : index j≠index k := fun he => hjk (index_injective he)
      simpa only [actualUnit,hi,hjk,ite_false] using hh
  · intro i j
    exact hstar (index i) (index j)
  · intro i
    exact (matrix_diagonal _ _ _ _ _ (index i)).trans (magic_diagonal S I hS h hm P hP i)
  · intro i j
    exact actual_units_centralize S I hS h hm P hP (index i) (index j)
  · simpa [actualUnit,index,Fin.sum_univ_succ,Fintype.sum_prod_type,add_assoc] using hsum

theorem flag_active_orthogonal {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    (P*flagA (normalOfPure S) I*P)*rowActive S I P 0=0 := by
  let B := compressed P (rowPOVM S I 0)
  have hflag : coarse B (cellClass false 0) 0=P*flagA (normalOfPure S) I*P := by
    norm_num [coarse,cellClass,cellSign,Fin.sum_univ_succ,B,compressed,rowPOVM,flagA,normalOfPure]
  have hact (a : Fin 6) : (P*flagA (normalOfPure S) I*P)*B a=
      if cellClass false 0 a=0 then B a else 0 := by
    rw [← hflag]
    exact coarse_action B _ _ P hP.1
      (compressed_positive P hP.1 _ (fun a => S.measurements.alice_pos _ _))
      (compressed_sum P hP.1 _ (hS.2.1 0)) (row_sharp S I hS h hm P hP 0 0 0) a
  change (P*flagA (normalOfPure S) I*P)*active B=0
  rw [active,mul_add,mul_add,mul_add,hact,hact,hact,hact]
  norm_num [cellClass,cellSign]

/-- All matrix-unit and corner-projection fields of Lemma 4.1 are constructed.
Only the three equations for the fixed transportA remain outside this theorem. -/
theorem bridge_matrix_units {s} (S : PureStrategy s) (I : FMSInstance s)
    (hS : ConditionalPerfect (normalOfPure S) I) (h : Density)
    (hm : MarginalA (normalOfPure S) h) (P : Op) (hP : SupportOf h P) :
    let f := P*flagA (normalOfPure S) I*P
    let m := fun i => P*magicA (normalOfPure S) I i*P
    ∃ (e : Op) (t : Fin 4 → Fin 4 → Op),Projection e ∧ e=f+∑ i,m i ∧
      (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
      (∀ i j,star (t i j)=t j i) ∧ (∀ i,t i i=m i) ∧ (∀ i j,Centralizes h.op (t i j)) := by
  obtain ⟨hprod,hstar,hdiag,hcentral,hsum⟩ := units_analysis S I hS h hm P hP
  have hf := (SharpEvents.conditional_flag_sharp S I hS h hm P hP).2.1
  have he := (PauliExtraction.actual_relations S I hS h hm P hP).projection
  have hfe := flag_active_orthogonal S I hS h hm P hP
  have hef : rowActive S I P 0*(P*flagA (normalOfPure S) I*P)=0 := by
    have hh := congrArg star hfe
    simpa only [star_mul,hf.1,he.1,show star (0:Op)=0 from star_zero Op] using hh
  refine ⟨P*flagA (normalOfPure S) I*P+rowActive S I P 0,actualUnit S I P,?_,?_,hprod,hstar,hdiag,hcentral⟩
  · constructor
    · exact (PauliMatrixUnits.op_star_add _ _).trans (congrArg₂ (fun A B : Op => A+B) hf.1 he.1)
    · rw [add_mul,mul_add,mul_add,hf.2,he.2,hfe,hef]
      abel
  · rw [← hsum]
    simp_rw [hdiag]

#print axioms bridge_matrix_units
end Sigma2.BridgeMatrixUnits
