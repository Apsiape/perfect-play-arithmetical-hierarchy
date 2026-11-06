import Sigma2.CompilerSoundnessGraphForm
import Sigma2.CompilerSoundnessExtraction

/-! Multiplication from the actual submitted triangles, on one common frame. -/
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace Sigma2.CompilerSoundnessTriangles
open Compiler CompilerScaffold CompilerSoundnessNames CompilerSoundnessRows
  CompilerSoundnessFrame CompilerSoundnessGraphs CompilerSoundnessGraphForm
  CompilerSoundnessExtraction Preliminaries

def FrameBlock (f : Fin 3 → Op) (a b : Fin 3) (u : Op) : Prop :=
  f a*u=u ∧ u*f b=u

theorem block_star (f : Fin 3 → Op) (hp : ∀ i,Projection (f i))
    (a b : Fin 3) (u : Op) (hs : FrameBlock f a b u) : FrameBlock f b a (star u) := by
  constructor
  · simpa only [star_mul,(hp b).1] using congrArg (fun X : Op => star X) hs.2
  · simpa only [star_mul,(hp a).1] using congrArg (fun X : Op => star X) hs.1

theorem block_left (f : Fin 3 → Op)
    (hf : ∀ i j,f i*f j=if i=j then f j else 0)
    (a b i : Fin 3) (u : Op) (hs : FrameBlock f a b u) :
    f i*u=if i=a then u else 0 := by
  calc
    _=f i*(f a*u) := by rw [hs.1]
    _=(f i*f a)*u := (mul_assoc _ _ _).symm
    _=_ := by rw [hf]; split_ifs with h <;> simp only [hs.1,zero_mul]

theorem block_right (f : Fin 3 → Op)
    (hf : ∀ i j,f i*f j=if i=j then f j else 0)
    (a b i : Fin 3) (u : Op) (hs : FrameBlock f a b u) :
    u*f i=if b=i then u else 0 := by
  calc
    _=(u*f b)*f i := by rw [hs.2]
    _=u*(f b*f i) := mul_assoc _ _ _
    _=_ := by
      rw [hf]
      split_ifs with h
      · subst i; exact hs.2
      · exact mul_zero _

theorem block_mul_zero (f : Fin 3 → Op)
    (hf : ∀ i j,f i*f j=if i=j then f j else 0)
    (a b c d : Fin 3) (u v : Op)
    (hu : FrameBlock f a b u) (hv : FrameBlock f c d v) (hne : b≠c) : u*v=0 := by
  calc
    _=(u*f b)*(f c*v) := by rw [hu.2,hv.1]
    _=u*(f b*f c)*v := by noncomm_ring
    _=0 := by rw [hf,if_neg hne,mul_zero,zero_mul]

/-- The 02 block of projectivity of the rational triangle is exactly uv=w. -/
theorem corner_triangle (f : Fin 3 → Op) (hp : ∀ i,Projection (f i))
    (hf : ∀ i j,f i*f j=if i=j then f j else 0)
    (u v w T : Op) (hu : FrameBlock f 0 1 u) (hv : FrameBlock f 1 2 v)
    (hw : FrameBlock f 0 2 w) (hT : Projection T)
    (hlin : (3:ℂ) • T=f 0+f 1+f 2+u+star u+v+star v+w+star w) : u*v=w := by
  let A := (3:ℂ) • T
  have hsU := block_star f hp 0 1 u hu
  have hsV := block_star f hp 1 2 v hv
  have hsW := block_star f hp 0 2 w hw
  have hquad : A*A=(3:ℂ) • A := by
    dsimp [A]
    rw [smul_mul_smul_comm,hT.2,smul_smul]
  have hrow : f 0*A=f 0+u+w := by
    change f 0*((3:ℂ) • T)=_
    rw [hlin]
    simp only [mul_add,hf,block_left f hf 0 1 0 u hu,block_left f hf 1 0 0 (star u) hsU,
      block_left f hf 1 2 0 v hv,block_left f hf 2 1 0 (star v) hsV,
      block_left f hf 0 2 0 w hw,block_left f hf 2 0 0 (star w) hsW]
    norm_num
  have hcol : A*f 2=f 2+v+w := by
    change ((3:ℂ) • T)*f 2=_
    rw [hlin]
    simp only [add_mul,hf,block_right f hf 0 1 2 u hu,block_right f hf 1 0 2 (star u) hsU,
      block_right f hf 1 2 2 v hv,block_right f hf 2 1 2 (star v) hsV,
      block_right f hf 0 2 2 w hw,block_right f hf 2 0 2 (star w) hsW]
    norm_num
  have h02 : f 0*A*f 2=w := by
    rw [hrow]
    simp only [add_mul,hf,block_right f hf 0 1 2 u hu,hw.2]
    norm_num
  have hcomp : (f 0+u+w)*(f 2+v+w)=w+u*v+w := by
    simp only [add_mul,mul_add,hf,block_left f hf 1 2 0 v hv,hw.1,
      block_right f hf 0 1 2 u hu,hw.2,
      block_mul_zero f hf 0 1 0 2 u w hu hw (by decide),
      block_mul_zero f hf 0 2 1 2 w v hw hv (by decide),
      block_mul_zero f hf 0 2 0 2 w w hw hw (by decide)]
    norm_num
  have heq : w+u*v+w=(3:ℂ) • w := by
    calc
      _=(f 0*A)*(A*f 2) := by rw [hrow,hcol,hcomp]
      _=f 0*(A*A)*f 2 := by noncomm_ring
      _=(3:ℂ) • w := by rw [hquad,mul_smul_comm,smul_mul_assoc,h02]
  calc
    u*v=(w+u*v+w)-(2:ℂ) • w := by module
    _=(3:ℂ) • w-(2:ℂ) • w := by rw [heq]
    _=w := by module

theorem graph_frame_block (F : ProjectionName → Op) (hp : ∀ n,Projection (F n))
    (w : Word) (k : ℕ) :
    F (.frame (pairs[k]?.getD (0,1)).1)*graphBlock F w k=graphBlock F w k ∧
      graphBlock F w k*F (.frame (pairs[k]?.getD (0,1)).2)=graphBlock F w k := by
  constructor
  · unfold graphBlock
    rw [← mul_assoc,← mul_assoc,(hp _).2]
  · unfold graphBlock
    rw [mul_assoc,mul_assoc,(hp _).2]
    exact (mul_assoc _ _ _).symm

/-- Projectivity of the submitted triangle forces actual block multiplication. -/
theorem triangle_composition (P : Presentation) (e : Op) (F : ProjectionName → Op)
    (hp : ∀ n,Projection (F n))
    (hframe : ∀ i j : Fin 3,F (.frame i.val)*F (.frame j.val)=
      if i=j then F (.frame j.val) else 0)
    (hrows : ∀ r ∈ rowList P,evalRow e F r=0)
    (u v w : Word) (hu : u ∈ words P) (hv : v ∈ words P) (hw : w ∈ words P)
    (htri : triangleRow u v w ∈ rowList P) :
    graphBlock F u 0*graphBlock F v 2=graphBlock F w 1 := by
  apply corner_triangle (fun i : Fin 3 => F (.frame i.val)) (fun i => hp _) hframe
    (graphBlock F u 0) (graphBlock F v 2) (graphBlock F w 1) (F (.triangle u v w))
  · simpa [FrameBlock,pairs] using graph_frame_block F hp u 0
  · simpa [FrameBlock,pairs] using graph_frame_block F hp v 2
  · simpa [FrameBlock,pairs] using graph_frame_block F hp w 1
  · exact hp _
  · have hh := triangle_sum P e F hp hframe hrows u v w hu hv hw htri
    rw [← frame_sum P e F hrows] at hh
    simpa [Fin.sum_univ_succ,add_assoc] using hh

theorem actual_triangle_composition {P : Presentation} (E : SupportedScaffold P)
    (u v w : Word) (hu : u ∈ words P) (hv : v ∈ words P) (hw : w ∈ words P)
    (htri : triangleRow u v w ∈ rowList P) :
    graphBlock (projectionA P E.strategy E.supportA) u 0*
      graphBlock (projectionA P E.strategy E.supportA) v 2=
        graphBlock (projectionA P E.strategy E.supportA) w 1 :=
  triangle_composition P E.supportA (projectionA P E.strategy E.supportA)
    E.sharpA E.frame.2.1 E.rowsA u v w hu hv hw htri

#print axioms corner_triangle
#print axioms triangle_composition
#print axioms actual_triangle_composition
end Sigma2.CompilerSoundnessTriangles
