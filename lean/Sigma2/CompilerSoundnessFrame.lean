import Sigma2.CompilerSoundnessRows
import Sigma2.CompilerSoundnessTrace

/-! The actual synchronized qutrit frame and the four calibrated named corners. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessFrame
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessBindings
  CompilerSoundnessRows Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials

def frameRow : RationalRow := row [(1,.frame 0),(1,.frame 1),(1,.frame 2)] (-1)

theorem frameRow_mem (P : Presentation) : frameRow ∈ rowList P := by
  simp only [rowList,List.mem_append]
  left; left; left; left
  simp [frameRow]

theorem frame_sum (P : Presentation) (e : Op) (F : ProjectionName → Op)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0) :
    (∑ i : Fin 3,F (.frame i.val))=e := by
  apply sub_eq_zero.mp
  calc
    _ = evalRow e F frameRow := by
      norm_num [evalRow,frameRow,row,Fin.sum_univ_succ] <;> module
    _ = 0 := hrows frameRow (frameRow_mem P)

theorem projection_partition {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Op) (he : Projection e) (F : ι → Op) (hp : ∀ i,Projection (F i))
    (hs : ∑ i,F i=e) (i j : ι) : F i*F j=if i=j then F j else 0 := by
  have hpos (k : ι) : Positive (F k) :=
    ContinuousLinearMap.IsPositive.of_isStarProjection ⟨(hp k).2,(hp k).1⟩
  have hc (k : ι) : CoarseCells.coarse F id k=F k := by simp [CoarseCells.coarse]
  have hh := FiniteSpectral.coarse_action F id i e he hpos hs
    (by rw [hc]; exact hp i) j
  simpa only [hc,id_eq,eq_comm] using hh

theorem actual_frame (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e)
    (hrows : ∀ r ∈ rowList P,evalRow e (projectionA P S e) r=0) :
    (∑ i : Fin 3,projectionA P S e (.frame i.val))=e ∧
      (∀ i j : Fin 3,projectionA P S e (.frame i.val)*projectionA P S e (.frame j.val)=
        if i=j then projectionA P S e (.frame j.val) else 0) ∧
      (∀ i : Fin 3,Centralizes h.op (projectionA P S e (.frame i.val))) := by
  have hs := frame_sum P e (projectionA P S e) hrows
  exact ⟨hs,projection_partition e he.1 (fun i : Fin 3 => projectionA P S e (.frame i.val))
    (fun i => sharpA P S hS h hm e he _) hs,fun i => centralA P S hS h hm e he _⟩

/-- The four bridges remain the original calibrated transport blocks after
identifying every named source and magic-corner parameter. -/
theorem named_calibration (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (g : Fin 4) :
    let w := e*transportA S (fmsInstance P g)*e
    ∃ (E : Op) (t : Fin 4 → Fin 4 → Op),
      Projection E ∧ E=projectionA P S e (.parameter (cornerIndex g.val))+
        ∑ i : Fin 4,projectionA P S e (.parameter (1+4*g.val+i.val)) ∧
      (∀ i j k l,t i j*t k l=if j=k then t i l else 0) ∧
      (∀ i j,star (t i j)=t j i) ∧
      (∀ i,t i i=projectionA P S e (.parameter (1+4*g.val+i.val))) ∧
      (∀ i j,Centralizes h.op (t i j)) ∧
      star w*w=projectionA P S e (.parameter (cornerIndex g.val)) ∧
      w*star w=projectionA P S e (.parameter (1+4*g.val)) ∧ h.op*w=(2:ℂ) • (w*h.op) := by
  have hh := CompilerSoundnessPadding.actual_bridge P S hS g h hm e he
  dsimp only [BridgeConclusion] at hh
  simpa only [flag_binding P S hS h hm e he,magic_binding P S hS h hm e he,Fin.val_zero,Nat.add_zero] using hh

theorem named_trace_recurrence (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e) (g k : Fin 4) :
    trace (h.op*projectionA P S e (.parameter (1+4*g.val+k.val)))=
      (2:ℂ)*trace (h.op*projectionA P S e (.parameter (cornerIndex g.val))) := by
  have hh := CompilerSoundnessTrace.actual_trace_recurrence P S hS g h hm e he k
  rwa [magic_binding P S hS h hm e he,flag_binding P S hS h hm e he] at hh

/-- Only the encoded corner-cover equation remains as an explicit premise. -/
theorem named_source_mass_of_cover (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e)
    (hcover : ∑ i : Fin 17,projectionA P S e (.parameter i.val)=e) :
    (trace (h.op*projectionA P S e (.parameter 0))).re=1/121 := by
  apply CompilerSoundnessTrace.source_mass_of_cover h e he
    (fun i : Fin 17 => projectionA P S e (.parameter i.val))
    (fun i => sharpA P S hS h hm e he _) hcover
  intro g k
  have hh := congrArg Complex.re (named_trace_recurrence P S hS h hm e he g k)
  simpa [Complex.mul_re] using hh

#print axioms frame_sum
#print axioms actual_frame
#print axioms named_calibration
#print axioms named_trace_recurrence
#print axioms named_source_mass_of_cover
end Sigma2.CompilerSoundnessFrame
