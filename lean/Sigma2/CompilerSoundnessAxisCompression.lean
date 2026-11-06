import Sigma2.CompilerSoundnessAxis
import Sigma2.CompilerSoundnessLift

/-! Source and target compression for the same two literal axes. -/
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessAxisCompression
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessExtraction
  CompilerSoundnessCopies CompilerSoundnessBlockEquations CompilerSoundnessAxis
  CompilerSoundnessCover CompilerSoundnessLift
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
variable {P : Presentation}

def axisOp (E : SupportedScaffold P) (g : Fin 4) (k : Fin 2) : Op :=
  E.supportA-magicSupport E g+cell E g (if k=0 then 1 else 0) 1

theorem magicSupport_supported (E : SupportedScaffold P) (g : Fin 4) :
    E.supportA*magicSupport E g=magicSupport E g ∧ magicSupport E g*E.supportA=magicSupport E g := by
  rw [magicSupport_eq]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => (projectionA_supported P E.strategy E.supportA E.supportA_laws.1 _).1)
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => (projectionA_supported P E.strategy E.supportA E.supportA_laws.1 _).2)

theorem target_magic (E : SupportedScaffold P) (g : Fin 4) :
    let C := parameter E (1+4*g.val)
    magicSupport E g*C=C ∧ C*magicSupport E g=C := by
  have h := cells_pairs E g
  rw [target_diagonal]
  change magicSupport E g*(PauliMatrixUnits.projector _ _ 0*PauliMatrixUnits.projector _ _ 0)=_ ∧
    (PauliMatrixUnits.projector _ _ 0*PauliMatrixUnits.projector _ _ 0)*magicSupport E g=_
  constructor
  · rw [← mul_assoc,(PauliMatrixUnits.projector_supported _ _ _ h.first 0).1]
    rfl
  · rw [mul_assoc,(PauliMatrixUnits.projector_supported _ _ _ h.second 0).2]
    rfl

theorem target_axis_edges (E : SupportedScaffold P) (g : Fin 4) (k : Fin 2) :
    let C := parameter E (1+4*g.val)
    C*axisOp E g k=C*cell E g (if k=0 then 1 else 0) 1 ∧
      axisOp E g k*C=cell E g (if k=0 then 1 else 0) 1*C := by
  have hs := projectionA_supported P E.strategy E.supportA E.supportA_laws.1 (.parameter (1+4*g.val))
  change E.supportA*parameter E (1+4*g.val)=_ ∧ parameter E (1+4*g.val)*E.supportA=_ at hs
  simp only [axisOp,mul_add,mul_sub,add_mul,sub_mul,hs,(target_magic E g).1,(target_magic E g).2,sub_self,zero_add]
  exact ⟨trivial,trivial⟩

theorem target_axis_sandwich (E : SupportedScaffold P) (g : Fin 4) :
    let C := parameter E (1+4*g.val)
    C*axisOp E g 0*C=0 ∧ C*axisOp E g 1*C=0 ∧ C*(axisOp E g 0*axisOp E g 1)*C=0 := by
  have h := target_cell_sandwich E g
  dsimp only at h ⊢
  refine ⟨?_,?_,?_⟩
  · rw [(target_axis_edges E g 0).1]
    exact h.1
  · rw [(target_axis_edges E g 1).1]
    exact h.2.1
  · calc
      _=(parameter E (1+4*g.val)*axisOp E g 0)*(axisOp E g 1*parameter E (1+4*g.val)) := by simp only [mul_assoc]
      _=(parameter E (1+4*g.val)*cell E g 1 1)*(cell E g 0 1*parameter E (1+4*g.val)) := by
        rw [(target_axis_edges E g 0).1,(target_axis_edges E g 1).2]
        rfl
      _=0 := by simpa only [mul_assoc] using h.2.2

theorem source_magic_zero (E : SupportedScaffold P) (g : Fin 4) :
    parameter E (cornerIndex g.val)*magicSupport E g=0 ∧
      magicSupport E g*parameter E (cornerIndex g.val)=0 := by
  have hc : cornerIndex g.val<17 := by
    have := g.isLt; unfold cornerIndex; split_ifs <;> omega
  have hz (k : Fin 4) : parameter E (cornerIndex g.val)*parameter E (1+4*g.val+k.val)=0 := by
    have hk : 1+4*g.val+k.val<17 := by have := g.isLt; have := k.isLt; omega
    have hn : (⟨cornerIndex g.val,hc⟩ : Fin 17)≠⟨1+4*g.val+k.val,hk⟩ := by
      intro he
      have hv := congrArg Fin.val he
      change cornerIndex g.val=1+4*g.val+k.val at hv
      have := g.isLt
      have := k.isLt
      unfold cornerIndex at hv
      split_ifs at hv <;> omega
    exact (CompilerSoundnessDecoded.corner_partition E ⟨_,hc⟩ ⟨_,hk⟩).trans (if_neg hn)
  have hl : parameter E (cornerIndex g.val)*magicSupport E g=0 := by
    rw [magicSupport_eq,Finset.mul_sum]
    exact Finset.sum_eq_zero (fun k _ => hz k)
  refine ⟨hl,?_⟩
  have hstar : star (magicSupport E g)=magicSupport E g := (cells_pairs E g).first.projection.1
  simpa only [parameter,star_mul,hstar,(E.sharpA _).1,show star (0:Op)=0 from star_zero Op] using congrArg (fun A : Op => star A) hl

theorem source_axis (E : SupportedScaffold P) (g : Fin 4) (k : Fin 2) :
    parameter E (cornerIndex g.val)*axisOp E g k=parameter E (cornerIndex g.val) ∧
      axisOp E g k*parameter E (cornerIndex g.val)=parameter E (cornerIndex g.val) := by
  have h := cells_pairs E g
  have hm : magicSupport E g*cell E g (if k=0 then 1 else 0) 1=cell E g (if k=0 then 1 else 0) 1 := by
    fin_cases k
    · exact h.first.eX
    · exact h.second.eX
  have hr : cell E g (if k=0 then 1 else 0) 1*magicSupport E g=cell E g (if k=0 then 1 else 0) 1 := by
    fin_cases k
    · exact h.first.Xe
    · exact h.second.Xe
  have hz : parameter E (cornerIndex g.val)*cell E g (if k=0 then 1 else 0) 1=0 := by
    rw [← hm,← mul_assoc,(source_magic_zero E g).1,zero_mul]
  have hz' : cell E g (if k=0 then 1 else 0) 1*parameter E (cornerIndex g.val)=0 := by
    rw [← hr,mul_assoc,(source_magic_zero E g).2,mul_zero]
  have hs := projectionA_supported P E.strategy E.supportA E.supportA_laws.1 (.parameter (cornerIndex g.val))
  change E.supportA*parameter E (cornerIndex g.val)=_ ∧ parameter E (cornerIndex g.val)*E.supportA=_ at hs
  simp only [axisOp,mul_add,mul_sub,add_mul,sub_mul,hs,(source_magic_zero E g).1,(source_magic_zero E g).2,hz,hz',sub_zero,add_zero]
  exact ⟨trivial,trivial⟩

#print axioms target_axis_sandwich
#print axioms source_axis
end Sigma2.CompilerSoundnessAxisCompression
