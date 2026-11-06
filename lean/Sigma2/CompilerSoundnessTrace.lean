import Sigma2.CompilerSoundnessPadding
import Sigma2.MatrixSupportDensity
import Sigma2.FockTrace

/-! Actual calibration gives trace recurrences for the submitted scaffold
operators. All trace manipulations use the proved summable density products. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessTrace
open Compiler CompilerScaffold Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

theorem modular_corner_trace (h : Density) (w f m : Op)
    (hf : star w*w=f) (hm : w*star w=m)
    (hw : h.op*w=(2:ℂ) • (w*h.op)) :
    trace (h.op*m)=(2:ℂ)*trace (h.op*f) := by
  have he : h.op*m=(2:ℂ) • (w*h.op*star w) := by
    rw [← hm,← mul_assoc,hw,smul_mul_assoc]
  rw [he,CompilerAlgebra.trace_smul,MatrixSupportCoordinates.sandwich_trace,hf]

theorem matrix_corner_trace (h : Density) (t : Fin 4 → Fin 4 → Op)
    (hp : ∀ i j k l,t i j*t k l=if j=k then t i l else 0)
    (ha : ∀ i j,star (t i j)=t j i)
    (hc : ∀ i j,Centralizes h.op (t i j)) (i j : Fin 4) :
    trace (h.op*t i i)=trace (h.op*t j j) := by
  have he : t i j*h.op*star (t i j)=h.op*t i i := by
    rw [← (hc i j),mul_assoc,ha,hp,if_pos rfl]
  have hh := MatrixSupportCoordinates.sandwich_trace h (t i j)
  rw [he,ha,hp,if_pos rfl] at hh
  exact hh

/-- Each of the four original magic corners has twice the flag trace,
from the actual calibrated block and actual matrix units. -/
theorem actual_trace_recurrence (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (g : Fin 4) (h : Density)
    (hm : MarginalA S h) (e : Op) (he : SupportOf h e) (i : Fin 4) :
    trace (h.op*(e*magicA S (fmsInstance P g) i*e))=
      (2:ℂ)*trace (h.op*(e*flagA S (fmsInstance P g)*e)) := by
  obtain ⟨E,t,hE,hEt,hp,ha,hd,hc,hwf,hwm,hw⟩ :=
    CompilerSoundnessPadding.actual_bridge P S hS g h hm e he
  have ht := matrix_corner_trace h t hp ha hc i 0
  rw [hd,hd] at ht
  exact ht.trans (modular_corner_trace h _ _ _ hwf hwm hw)

/-- A genuine orthogonal cover, once identified with the actual calibrated
corners, has the required source mass. No formal cyclic trace rule is assumed. -/
theorem source_mass_of_cover (h : Density) (e : Op) (he : SupportOf h e)
    (C : Fin 17 → Op) (hp : ∀ i,Projection (C i)) (hcover : ∑ i,C i=e)
    (hcal : ∀ g k : Fin 4,
      (trace (h.op*C ⟨1+4*g.val+k.val,by have := g.isLt; have := k.isLt; omega⟩)).re=
        2*(trace (h.op*C ⟨cornerIndex g.val,by have := g.isLt; unfold cornerIndex; split_ifs <;> omega⟩)).re) :
    (trace (h.op*C 0)).re=1/121 := by
  have hpos (i : Fin 17) : Positive (C i) := by
    exact ContinuousLinearMap.IsPositive.of_isStarProjection ⟨(hp i).2,(hp i).1⟩
  have ht : ∑ i : Fin 17,(trace (h.op*C i)).re=1 := by
    rw [← Complex.re_sum,← FockTrace.trace_density_sum h Finset.univ C (fun i _ => hpos i),hcover]
    have hr : h.op*e=h.op := (MatrixCentralizer.support_centralizes h e he).eq.trans he.2.1
    rw [hr,FockTrace.trace_density_re]
  have h00 := hcal 0 0; have h01 := hcal 0 1; have h02 := hcal 0 2; have h03 := hcal 0 3
  have h10 := hcal 1 0; have h11 := hcal 1 1; have h12 := hcal 1 2; have h13 := hcal 1 3
  have h20 := hcal 2 0; have h21 := hcal 2 1; have h22 := hcal 2 2; have h23 := hcal 2 3
  have h30 := hcal 3 0; have h31 := hcal 3 1; have h32 := hcal 3 2; have h33 := hcal 3 3
  norm_num [cornerIndex] at h00 h01 h02 h03 h10 h11 h12 h13 h20 h21 h22 h23 h30 h31 h32 h33
  norm_num [Fin.sum_univ_succ] at ht
  linarith

#print axioms modular_corner_trace
#print axioms matrix_corner_trace
#print axioms actual_trace_recurrence
#print axioms source_mass_of_cover
end Sigma2.CompilerSoundnessTrace
