import Sigma2.CompilerSoundnessFrame

/-! Actual off-diagonal graph extraction from the finite row dictionary.
These are the concrete rational 3-4-5 rows of the frozen compiler. -/
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessGraphs
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows CompilerSoundnessFrame
  Preliminaries
attribute [local irreducible] CompilerScaffold.names CompilerScaffold.rowList
  CompilerScaffold.words CompilerScaffold.polynomials
  CompilerScaffold.structuralPolynomials CompilerScaffold.applicationPolynomials
  CompilerScaffold.graphRows CompilerScaffold.wordRows

theorem wordRow_mem (P : Presentation) (w : Word) (hw : w ∈ words P)
    (r : RationalRow) (hr : r ∈ wordRows w) : r ∈ rowList P := by
  simp only [rowList,List.mem_append]
  left; left; right
  exact List.mem_flatMap.mpr ⟨w,hw,hr⟩

theorem graphRow_mem (P : Presentation) (w : Word) (hw : w ∈ words P)
    (k : Fin 3) (r : RationalRow) (hr : r ∈ graphRows w k.val) : r ∈ rowList P := by
  apply wordRow_mem P w hw r
  change r ∈ wordRows w
  unfold CompilerScaffold.wordRows
  simp only [List.mem_append]
  left; left; left
  exact List.mem_flatMap.mpr ⟨k.val,List.mem_range.mpr k.isLt,hr⟩

theorem graph_equations (e : Op) (F : ProjectionName → Op) (w : Word) (k : ℕ)
    (hrows : ∀ r ∈ graphRows w k,evalRow e F r=0) :
    let ij := pairs[k]?.getD (0,1)
    F (.graph w k 0)+F (.graph w k 1)=F (.frame ij.1)+F (.frame ij.2) ∧
    F (.graph w k 2)+F (.graph w k 3)=F (.frame ij.1)+F (.frame ij.2) ∧
    (5:ℂ) • F (.graph w k 2)+F (.frame ij.1)+F (.frame ij.2)=
      (3:ℂ) • F (.frame ij.1)+(4:ℂ) • F (.graph w k 0) := by
  let ij := pairs[k]?.getD (0,1)
  have h0 := hrows (row [(1,.graph w k 0),(1,.graph w k 1),(-1,.frame ij.1),(-1,.frame ij.2)])
    (by simp [graphRows,ij])
  have h1 := hrows (row [(1,.graph w k 2),(1,.graph w k 3),(-1,.frame ij.1),(-1,.frame ij.2)])
    (by simp [graphRows,ij])
  have h2 := hrows (row [(5,.graph w k 2),(-2,.frame ij.1),(1,.frame ij.2),(-4,.graph w k 0)])
    (by simp [graphRows,ij])
  refine ⟨?_,?_,?_⟩
  · apply sub_eq_zero.mp
    calc
      _ = evalRow e F (row [(1,.graph w k 0),(1,.graph w k 1),(-1,.frame ij.1),(-1,.frame ij.2)]) := by
        simp [evalRow,row] <;> module
      _ = 0 := h0
  · apply sub_eq_zero.mp
    calc
      _ = evalRow e F (row [(1,.graph w k 2),(1,.graph w k 3),(-1,.frame ij.1),(-1,.frame ij.2)]) := by
        simp [evalRow,row] <;> module
      _ = 0 := h1
  · apply sub_eq_zero.mp
    calc
      _ = evalRow e F (row [(5,.graph w k 2),(-2,.frame ij.1),(1,.frame ij.2),(-4,.graph w k 0)]) := by
        simp [evalRow,row] <;> module
      _ = 0 := h2

def graphBlock (F : ProjectionName → Op) (w : Word) (k : ℕ) : Op :=
  let ij := pairs[k]?.getD (0,1)
  F (.frame ij.1)*((2:ℂ) • F (.graph w k 0)-(F (.frame ij.1)+F (.frame ij.2)))*F (.frame ij.2)

/-- The extracted block is the actual named graph's off diagonal. -/
theorem graph_isometry (e : Op) (F : ProjectionName → Op) (hp : ∀ n,Projection (F n))
    (w : Word) (k : ℕ) (hrows : ∀ r ∈ graphRows w k,evalRow e F r=0)
    (horth : F (.frame (pairs[k]?.getD (0,1)).1)*F (.frame (pairs[k]?.getD (0,1)).2)=0) :
    star (graphBlock F w k)*graphBlock F w k=F (.frame (pairs[k]?.getD (0,1)).2) ∧
      graphBlock F w k*star (graphBlock F w k)=F (.frame (pairs[k]?.getD (0,1)).1) := by
  obtain ⟨h0,h1,h2⟩ := graph_equations e F w k hrows
  exact Compiler.graph_certificate _ _ _ _ _ _ (hp _) (hp _) horth
    (hp _) (hp _) (hp _) (hp _) h0 h1 h2

/-- K3's three graph blocks for every concrete retained word, with no graph
certificate or unitary supplied as a hypothesis. -/
theorem actual_graph_isometry (P : Presentation) (S : NormalStrategy (scenario P))
    (hS : Perfect (preGame P) S) (h : Density) (hm : MarginalA S h)
    (e : Op) (he : SupportOf h e)
    (hrows : ∀ r ∈ rowList P,evalRow e (projectionA P S e) r=0)
    (w : Word) (hw : w ∈ words P) (k : Fin 3) :
    star (graphBlock (projectionA P S e) w k.val)*graphBlock (projectionA P S e) w k.val=
        projectionA P S e (.frame (pairs[k.val]?.getD (0,1)).2) ∧
      graphBlock (projectionA P S e) w k.val*star (graphBlock (projectionA P S e) w k.val)=
        projectionA P S e (.frame (pairs[k.val]?.getD (0,1)).1) := by
  apply graph_isometry e (projectionA P S e) (sharpA P S hS h hm e he) w k.val
    (fun r hr => hrows r (graphRow_mem P w hw k r hr))
  have hf := (actual_frame P S hS h hm e he hrows).2.1
  fin_cases k
  · simpa [pairs] using hf 0 1
  · simpa [pairs] using hf 0 2
  · simpa [pairs] using hf 1 2

#print axioms graph_equations
#print axioms graph_isometry
#print axioms actual_graph_isometry
end Sigma2.CompilerSoundnessGraphs
