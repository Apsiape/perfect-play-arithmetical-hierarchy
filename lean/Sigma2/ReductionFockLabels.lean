import Sigma2.ReductionFockSymbols

noncomputable section
open scoped BigOperators InnerProductSpace Classical ENNReal
set_option maxHeartbeats 300000
namespace Sigma2.ReductionFockModel
open Sigma2.Tree FockModel Sigma2.Reduction
variable (q : ℕ) [NeZero q] (M : Automaton) (ζ : ℂ) (hnorm : ‖ζ‖=1)
  (hsep : ∀ y, 0<y → ¬q∣y → (1/2:ℝ)^(y+1)≤‖ζ^y-1‖)

lemma types_length : (applicationPresentation M).types.length=M.extraSymbols+15 := by
  change (([.projection,.unitary,.unitary,.projection,.projection,.unitary,.positive,
    .unitary,.unitary,.unitary,.projection,.contraction] : List LabelType) ++
    List.replicate (M.extraSymbols+3) LabelType.projection).length=M.extraSymbols+15
  simp

def label : ℕ → Op
  | 0 => root q
  | 1 => ux q
  | 2 => uy q
  | 3 => px q
  | 4 => py q
  | 5 => wave q ζ hnorm
  | 6 => counter q
  | 7 => phaseOp q ζ
  | 8 => jOp q
  | 9 => kOp q ζ hnorm
  | 10 => pulse q
  | 11 => inverseReader q ζ hsep
  | i+12 => if h : i<M.extraSymbols+3 then symbol q M ⟨i,h⟩ else 0

@[simp] lemma label_symbol (c : Symbol M) :
    label q M ζ hnorm hsep (12+c.val)=symbol q M c := by
  simpa [Nat.add_comm,label,c.isLt]

lemma root_centralizer : Centralizes (density q).op (root q) := by
  apply ambient_ext q
  intro u
  by_cases h : u.1=[] <;> simp only [mul_apply_eq_comp,root_basis,density_basis,map_smul,map_zero,
    apply_ite,h,ite_true,ite_false,smul_zero]

lemma label_typed (i : ℕ) (hi : i<M.extraSymbols+15) :
    TypedAt 1 (label q M ζ hnorm hsep i)
      ((applicationPresentation M).types[i]'(by rw [types_length M]; exact hi)) := by
  by_cases h : i<12
  · interval_cases i
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using root_projection q
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using ux_unitary q
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using uy_unitary q
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using px_projection q
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using py_projection q
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using wave_unitary q ζ hnorm
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using counter_positive q
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using phase_unitary q ζ hnorm
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using j_unitary q
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using k_unitary q ζ hnorm
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using pulse_projection q
    · simpa [applicationPresentation,buildPresentation,label,TypedAt,Unitary,PositiveContraction] using inverseReader_contraction q ζ hsep
  · have hb : i-12<M.extraSymbols+3 := by omega
    have he : i=(i-12)+12 := by omega
    have ho : (applicationPresentation M).types[i]?=some LabelType.projection := by
      change (([.projection,.unitary,.unitary,.projection,.projection,.unitary,.positive,
        .unitary,.unitary,.unitary,.projection,.contraction] : List LabelType) ++
        List.replicate (M.extraSymbols+3) LabelType.projection)[i]?=some LabelType.projection
      rw [List.getElem?_append_right (by simp; omega)]
      simp [hb]
    have ht : (applicationPresentation M).types[i]'(by rw [types_length M]; exact hi)=.projection := by
      obtain ⟨hidx,helem⟩ := List.getElem?_eq_some_iff.mp ho
      exact helem
    rw [ht]
    change Projection (label q M ζ hnorm hsep i)
    rw [he]
    simpa only [label,dif_pos hb] using symbol_projection q M ⟨i-12,hb⟩

lemma label_centralizer (i : ℕ) : Centralizes (density q).op (label q M ζ hnorm hsep i) := by
  by_cases h : i<12
  · interval_cases i
    · exact root_centralizer q
    · exact ux_centralizer q
    · exact uy_centralizer q
    · exact px_centralizer q
    · exact py_centralizer q
    · exact wave_centralizer q ζ hnorm
    · exact counter_centralizer q
    · exact phase_centralizer q ζ
    · exact j_centralizer q
    · exact k_centralizer q ζ hnorm
    · exact pulse_centralizer q
    · exact inverseReader_centralizer q ζ hsep
  · have he : i=(i-12)+12 := by omega
    rw [he]
    simp only [label]
    split_ifs
    · exact symbol_centralizer q M _
    · simp [Centralizes]

#print axioms label_typed
#print axioms label_centralizer
end Sigma2.ReductionFockModel
