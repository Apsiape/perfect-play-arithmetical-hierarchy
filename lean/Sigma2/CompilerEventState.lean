import Sigma2.MagicRelations
import Sigma2.RowColumns
import Sigma2.FiniteAncillaMatrix
import Sigma2.FiniteAncillaDensity
import Sigma2.Preliminaries

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators InnerProductSpace
namespace Sigma2.CompilerEventState
open Coefficients TensorLifts FiniteSum FiniteAncilla

/-- Local expectation against an arbitrary normal ensemble equals the trace
against its actual marginal. Absolute covariance summability justifies tsums. -/
theorem normal_expectation {s} (S : NormalStrategy s) (h : Density)
    (hm : MarginalA S h) (B : Op) (hB : Positive B) :
    (∑' k,S.weight k*(inner ℂ (S.vector k) (left B (S.vector k))).re)=
      (trace (h.op*B)).re := by
  let w : ℕ → AB := fun k => (Real.sqrt (S.weight k):ℂ) • S.vector k
  let u : ℕ × ℕ → H := fun p => column (w p.1) p.2
  have hu : Summable (fun p => ‖u p‖^2) := by
    apply (summable_prod_of_nonneg (fun _ => sq_nonneg _)).mpr
    refine ⟨fun k => (column_mass (w k)).1,?_⟩
    have he k : (∑' j,‖u (k,j)‖^2)=S.weight k :=
      (column_mass (w k)).2.trans
        (weighted_unit_norm _ (S.weight_nonneg k) _ (S.unit k))
    simpa only [he] using S.weight_summable
  have ht := TraceProducts.covariance_mul_trace u hu B hB
  have hc : h.op=covariance u := EntropyComponentBounds.normal_marginalA_covariance S h hm
  rw [hc,ht.2.1,ht.2.2.tsum_prod]
  change _=Complex.reCLM (∑' k,∑' j,inner ℂ (B (u (k,j))) (u (k,j)))
  rw [Complex.reCLM.map_tsum ht.2.2.prod]
  apply tsum_congr
  intro k
  have he : (∑' j,inner ℂ (B (u (k,j))) (u (k,j)))=
      inner ℂ (left B (w k)) (w k) := by
    rw [inner_columns]
    simp only [column_left]
    rfl
  rw [he]
  change _=(inner ℂ (left B (w k)) (w k)).re
  have hs : (inner ℂ (left B (w k)) (w k)).re=(inner ℂ (w k) (left B (w k))).re := inner_re_symm (𝕜 := ℂ) _ _
  rw [hs]
  dsimp only [w]
  rw [Purification.weighted_expectation _ (S.weight_nonneg k)]
  simp

/-- Zero Walsh column, with blocks V_i V_j*/d. No bit count is required. -/
def zeroColumn {d : ℕ} (V : Fin d → Op) : Matrix (Fin d) (Fin d) Op :=
  fun i j => (1/(d:ℂ)) • (V i*star (V j))

def zeroReference (d : ℕ) : Matrix (Fin d) (Fin d) Op :=
  fun _ _ => (1/(d:ℂ)) • (1:Op)

theorem zeroColumn_projection {d : ℕ} [NeZero d] (V : Fin d → Op)
    (hV : ∀ j,Unitary (V j)) : Projection (matrixOp d (zeroColumn V)) := by
  have he : zeroColumn V=RowColumns.column 0 V 0 := by
    ext i j
    simp [zeroColumn,RowColumns.column,RowGame.parity,RowColumns.sign]
  rw [he]
  exact matrixOp_projection d _ (RowColumns.column_star _ _ _)
    (RowColumns.column_idempotent (Nat.pos_of_ne_zero (NeZero.ne d)) _ _ hV _)

/-- The uniform reference is its own finite transpose and mirrors on every
entangled old vector; this property does not constrain the old state. -/
theorem reference_mirror (d : ℕ) [NeZero d] (v : AB) :
    left (matrixOp d (zeroReference d)) (entangle d v)=
      right (matrixOp d (zeroReference d)) (entangle d v) := by
  apply matrix_mirror
  intro a b
  simp only [zeroReference,MagicRelations.left_smul,MagicRelations.right_smul,
    left_one,right_one]

/-- Direct ancillary contraction, before the mixed ensemble or trace.
The column convention naturally gives T T*. A selfadjoint slot sum changes
this to T* T in the event theorem. -/
theorem entangled_zero_expectation (d : ℕ) [NeZero d] (V : Fin d → Op) (v : AB) :
    inner ℂ (entangle d v)
      (left (matrixOp d (zeroColumn V))
        (right (matrixOp d (zeroReference d)) (entangle d v)))=
      (1/(d:ℂ)^3)*inner ℂ v (left ((∑ j,V j)*star (∑ j,V j)) v) := by
  rw [inner_fibers (bipCoordinates d),Fintype.sum_prod_type]
  have hf (a b : Fin d) :
      fiber (bipCoordinates d)
        (left (matrixOp d (zeroColumn V))
          (right (matrixOp d (zeroReference d)) (entangle d v))) (a,b)=
      ∑ c, amplitude d • left ((1/(d:ℂ)^2) • (V a*star (V c))) v := by
    rw [fiber_left_matrixOp]
    simp only [right_matrix_entangle,zeroColumn,zeroReference,
      MagicRelations.right_smul,right_one,smul_apply,one_apply_eq_self,map_smul,
      MagicRelations.left_smul]
    apply Finset.sum_congr rfl
    intro c hc
    simp only [smul_smul]
    congr 1
    field_simp
    <;> ring
  simp_rw [fiber_entangle,hf,inner_sum]
  have he (a b c : Fin d) :
      inner ℂ (if a=b then amplitude d • v else 0)
        (amplitude d • left ((1/(d:ℂ)^2) • (V a*star (V c))) v)=
      if a=b then (1/(d:ℂ)^3)*inner ℂ v (left (V a*star (V c)) v) else 0 := by
    by_cases hab : a=b
    · subst b
      simp only [ite_true,inner_smul_left,inner_smul_right,
        MagicRelations.left_smul,smul_apply]
      change amplitude d*((1/(d:ℂ)^2)*(star (amplitude d)*inner ℂ v (left (V a*star (V c)) v)))=_
      calc
        _=(amplitude d*amplitude d)*((1/(d:ℂ)^2)*inner ℂ v (left (V a*star (V c)) v)) := by
          rw [amplitude_star]
          ring
        _=_ := by rw [amplitude_square]; push_cast; ring
    · simp only [hab,ite_false,inner_zero_left]
  simp_rw [he]
  simp_rw [Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero]
  have hs (a : Fin d) :
      (∑ b,if a=b then ∑ c,(1/(d:ℂ)^3)*inner ℂ v (left (V a*star (V c)) v) else 0)=
      ∑ c,(1/(d:ℂ)^3)*inner ℂ v (left (V a*star (V c)) v) := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b hb hba; simp [Ne.symm hba]
    · simp
  simp_rw [hs,← Finset.mul_sum]
  congr 1
  have hstar : star (∑ j,V j)=∑ j,star (V j) :=
    map_sum (starAddEquiv : Op ≃+ Op) V Finset.univ
  rw [hstar,Finset.sum_mul]
  rw [left_sum,sum_apply,inner_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum,left_sum,sum_apply,inner_sum]

#print axioms normal_expectation
#print axioms zeroColumn
#print axioms zeroReference
#print axioms zeroColumn_projection
#print axioms reference_mirror
#print axioms entangled_zero_expectation
end Sigma2.CompilerEventState



