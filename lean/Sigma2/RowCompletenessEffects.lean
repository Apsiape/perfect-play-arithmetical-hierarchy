import Sigma2.RowCompletenessFamily

set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns FiniteAncilla

/-- Padding is exactly the original fine effect at an injectively encoded answer. -/
theorem pad_effect {ι : Type} [Fintype ι] [DecidableEq ι] (P : Partition Op ι)
    (N : ℕ) (num : ι → ℕ) (hn : ∀ i,num i<N) (hi : Function.Injective num)
    (i : ι) (a : Fin N) (ha : a.val=num i) : (padPartition P N num hn).effect a=P.effect i := by
  have he : a=⟨num i,hn i⟩ := Fin.ext ha
  rw [he]
  apply Partition.coarse_injective
  intro i j hij
  exact hi (congrArg Fin.val hij)

theorem bit_injective : Function.Injective bit := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]

theorem bitAnswer_injective : Function.Injective bitAnswer := by
  intro a b h
  cases a <;> cases b <;> simp_all [bitAnswer]

theorem bitAnswer_lt (b : Bool) : bitAnswer b<2 := by cases b <;> decide

theorem twoDigit_injective (f g : Bool → ℕ) (hf : Function.Injective f) (hg : Function.Injective g)
    (hfb : ∀ b,f b<2) (hgb : ∀ b,g b<2) :
    Function.Injective (fun a : Bool × Bool => 2*f a.1+g a.2) := by
  intro a b he
  change 2*f a.1+g a.2=2*f b.1+g b.2 at he
  have h1 := hfb a.1; have h2 := hfb b.1; have h3 := hgb a.2; have h4 := hgb b.2
  apply Prod.ext
  · apply hf; omega
  · apply hg; omega

theorem pairNum_injective (d : ℕ) :
    Function.Injective (fun a : Bool × Fin d => 2*a.2.val+bit a.1) := by
  intro a b he
  change 2*a.2.val+bit a.1=2*b.2.val+bit b.1 at he
  have ha := bit_lt a.1; have hb := bit_lt b.1
  apply Prod.ext
  · apply bit_injective; omega
  · apply Fin.ext; omega

theorem slotNum_injective :
    Function.Injective (fun a : Bool × Fin 3 => 3*bit a.1+a.2.val) := by
  intro a b he
  change 3*bit a.1+a.2.val=3*bit b.1+b.2.val at he
  have ha := a.2.isLt; have hb := b.2.isLt
  apply Prod.ext
  · apply bit_injective; omega
  · apply Fin.ext; omega

def spectralEffect (U : Op) (b : Bool) : Op := (1/2:ℂ) • (1+sign b • U)
def binaryEffect (E : Op) (b : Bool) : Op := if b then E else 1-E

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

theorem cell_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (g : Fin (RowSlots.squares R)) (x y : Fin 3)
    (b : Bool) (a : AA (scenario G R)) (ha : a.val=bitAnswer b) :
    (newPartition G R E hE (.cell g x y)).effect a=spectralEffect (rowMagic R g x y) b := by
  apply pad_effect (hi:=bitAnswer_injective) (i:=b) (ha:=ha)

theorem line_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (g : Fin (RowSlots.squares R)) (col : Bool) (k : Fin 3)
    (b : Bool × Bool) (a : AA (scenario G R)) (ha : a.val=2*bit b.1+bit b.2) :
    (newPartition G R E hE (.line g col k)).effect a=
      spectralEffect (if col then rowMagic R g 0 k else rowMagic R g k 0) b.1*
      spectralEffect (if col then rowMagic R g 1 k else rowMagic R g k 1) b.2 := by
  apply pad_effect (hi:=twoDigit_injective bit bit bit_injective bit_injective bit_lt bit_lt) (i:=b) (ha:=ha)

theorem cross_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (g h : Fin (RowSlots.squares R)) (hgh : g≠h) (k l : Fin 4)
    (b : Bool × Bool) (a : AA (scenario G R)) (ha : a.val=2*bitAnswer b.1+bitAnswer b.2) :
    (newPartition G R E hE (.cross g h k l)).effect a=
      spectralEffect (rowAxis R g k) b.1*spectralEffect (rowAxis R h l) b.2 := by
  simp only [newPartition,dif_neg hgh]
  apply pad_effect (hi:=twoDigit_injective bitAnswer bitAnswer bitAnswer_injective bitAnswer_injective
    bitAnswer_lt bitAnswer_lt) (i:=b) (ha:=ha)

theorem oldAxis_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (i : Fin R.count) (g : Fin (RowSlots.squares R)) (k : Fin 4)
    (b : Bool × Bool) (a : AA (scenario G R)) (ha : a.val=2*bit b.1+bitAnswer b.2) :
    (newPartition G R E hE (.oldAxis i g k)).effect a=
      binaryEffect (amplify (RowSlots.dimension R) (E i)) b.1*spectralEffect (rowAxis R g k) b.2 := by
  apply pad_effect (hi:=twoDigit_injective bit bitAnswer bit_injective bitAnswer_injective
    bit_lt bitAnswer_lt) (i:=b) (ha:=ha)

theorem globalZ_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (b : Fin (2^(bits R))) (a : AA (scenario G R)) (ha : a.val=b.val) :
    (newPartition G R E hE (.global false)).effect a=
      (realizePartition (diagonalPartition (2^(bits R)))).effect b := by
  apply pad_effect (hi:=Fin.val_injective) (i:=b) (ha:=ha)

theorem globalX_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (b : Fin (2^(bits R))) (a : AA (scenario G R)) (ha : a.val=b.val) :
    (newPartition G R E hE (.global true)).effect a=(realizePartition (fourierPartition (bits R))).effect b := by
  apply pad_effect (hi:=Fin.val_injective) (i:=b) (ha:=ha)

theorem pair_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (j : ℕ) (hj : j<2^(bits R))
    (b : Bool × Fin (2^(bits R))) (a : AA (scenario G R)) (ha : a.val=2*b.2.val+bit b.1) :
    (newPartition G R E hE (.pair j)).effect a=(realizePartition (pairPartition (bits R) j hj)).effect b := by
  simp only [newPartition,dif_pos hj]
  apply pad_effect (hi:=pairNum_injective _) (i:=b) (ha:=ha)

theorem slot_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (j : ℕ) (hj : j<2^(bits R))
    (b : Bool × Fin 3) (a : AA (scenario G R)) (ha : a.val=3*bit b.1+b.2.val) :
    (newPartition G R E hE (.slot r j)).effect a=
      (realizePartition (slotPartition (bits R) j hj (slotEvent R E r j) (slotEvent_projection R E hE r j))).effect b := by
  simp only [newPartition,dif_pos hj]
  apply pad_effect (P:=realizePartition (slotPartition (bits R) j hj (slotEvent R E r j) (slotEvent_projection R E hE r j))) (hi:=slotNum_injective) (i:=b) (ha:=ha)

theorem column_effect (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) (b : Fin (RowSlots.dimension R))
    (a : AA (scenario G R)) (ha : a.val=b.val) :
    (newPartition G R E hE (.column r)).effect a=columnEffect R E r b := by
  apply pad_effect (hi:=Fin.val_injective) (i:=b) (ha:=ha)

end Sigma2.RowCompleteness
