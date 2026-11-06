import Sigma2.RowCompletenessPartitions
import Sigma2.RowCompletenessAssembly

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler RowGame TensorLifts FiniteAncilla

/-- A finite local POVM, allowing the unchanged old effects to be unsharp. -/
structure POVM (ι : Type) [Fintype ι] where
  effect : ι → Op
  positive : ∀ i,Positive (effect i)
  total : ∑ i,effect i=1

namespace POVM
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def coarse [DecidableEq κ] (P : POVM ι) (f : ι → κ) : POVM κ where
  effect k := ∑ i,if f i=k then P.effect i else 0
  positive k := by
    apply ContinuousLinearMap.nonneg_iff_isPositive.mp
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact ContinuousLinearMap.nonneg_iff_isPositive.mpr (P.positive i)
    · exact le_rfl
  total := by
    classical
    rw [Finset.sum_comm]
    simpa using P.total

theorem coarse_injective [DecidableEq κ] (P : POVM ι) (f : ι → κ)
    (hf : Function.Injective f) (i : ι) : (P.coarse f).effect (f i)=P.effect i := by
  classical
  change (∑ j,if f j=f i then P.effect j else 0)=_
  simp only [hf.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

theorem coarse_outside [DecidableEq κ] (P : POVM ι) (f : ι → κ)
    (k : κ) (hk : ∀ i,f i≠k) : (P.coarse f).effect k=0 := by
  change (∑ i,if f i=k then P.effect i else 0)=0
  simp [hk]

end POVM

def Partition.toPOVM {ι : Type} [Fintype ι] [DecidableEq ι] (P : Partition Op ι) : POVM ι :=
  ⟨P.effect,P.positive,P.total⟩

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

/-- One unchanged old Alice question, padded by genuine zero effects. -/
def paddedAlice (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (x : QA G.scenario) : POVM (AA (scenario G R)) :=
  (POVM.mk (fun a => amplify (RowSlots.dimension R) (M.alice x a))
    (fun a => amplify_positive _ _ (M.alice_pos x a)) (by
      rw [← amplify_sum,M.alice_sum,amplify_one])).coarse (embedding G R).aA

/-- One unchanged old Bob question, with the same shared ancillary identity. -/
def paddedBob (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (y : QB G.scenario) : POVM (BB (scenario G R)) :=
  (POVM.mk (fun b => amplify (RowSlots.dimension R) (M.bob y b))
    (fun b => amplify_positive _ _ (M.bob_pos y b)) (by
      rw [← amplify_sum,M.bob_sum,amplify_one])).coarse (embedding G R).aB

/-- A single simultaneous full-scenario measurement assignment. The same
ancillary register is used on all old and all new questions. -/
def assembleMeasurements (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (A : Q R → POVM (AA (scenario G R))) (B : Q R → POVM (BB (scenario G R))) :
    Measurements (scenario G R) :=
  let localA := fun x => match decodeA G R x with
    | .inl x => paddedAlice G R M x
    | .inr q => A q
  let localB := fun y => match decodeB G R y with
    | .inl y => paddedBob G R M y
    | .inr q => B q
  TensorLifts.measurements _ (fun x => (localA x).effect) (fun y => (localB y).effect)
    (fun x => (localA x).positive) (fun y => (localB y).positive)
    (fun x => (localA x).total) (fun y => (localB y).total)

theorem assembleMeasurements_oldA (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (A : Q R → POVM (AA (scenario G R))) (B : Q R → POVM (BB (scenario G R)))
    (x : QA G.scenario) (a : AA G.scenario) :
    (assembleMeasurements G R M A B).alice ((embedding G R).qA x) ((embedding G R).aA a)=
      amplify (RowSlots.dimension R) (M.alice x a) := by
  change (match decodeA G R ((embedding G R).qA x) with
    | .inl x => paddedAlice G R M x | .inr q => A q).effect ((embedding G R).aA a)=_
  rw [decodeA_old]
  exact POVM.coarse_injective _ _ (embedding G R).iaA a

theorem assembleMeasurements_oldB (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (A : Q R → POVM (AA (scenario G R))) (B : Q R → POVM (BB (scenario G R)))
    (y : QB G.scenario) (b : BB G.scenario) :
    (assembleMeasurements G R M A B).bob ((embedding G R).qB y) ((embedding G R).aB b)=
      amplify (RowSlots.dimension R) (M.bob y b) := by
  change (match decodeB G R ((embedding G R).qB y) with
    | .inl y => paddedBob G R M y | .inr q => B q).effect ((embedding G R).aB b)=_
  rw [decodeB_old]
  exact POVM.coarse_injective _ _ (embedding G R).iaB b

end Sigma2.RowCompleteness
