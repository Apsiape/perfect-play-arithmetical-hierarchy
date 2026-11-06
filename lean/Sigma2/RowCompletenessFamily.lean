import Sigma2.RowCompletenessMagic
import Sigma2.RowCompletenessSpectral
import Sigma2.RowCompletenessSupport

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
noncomputable section
open scoped BigOperators
namespace Sigma2.RowCompleteness
open Compiler RowGame RowColumns RowWalsh FiniteAncilla

local instance {s} (R : Rows s) : NeZero (RowSlots.dimension R) :=
  ⟨ne_of_gt (RowSlots.dimension_pos R)⟩

abbrev bits {s} (R : Rows s) := 2*RowSlots.squares R

def bit (b : Bool) : ℕ := if b then 1 else 0

theorem bit_lt (b : Bool) : bit b<2 := by cases b <;> decide

def squareBit {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 2) : Fin (bits R) :=
  ⟨2*g.val+k.val,by have := g.isLt; have := k.isLt; dsimp [bits]; omega⟩

def rowMagic {s} (R : Rows s) (g : Fin (RowSlots.squares R)) : Fin 3 → Fin 3 → Op :=
  magicCells (scalarX (bits R) (squareBit R g 0)) (scalarZ (bits R) (squareBit R g 0))
    (scalarX (bits R) (squareBit R g 1)) (scalarZ (bits R) (squareBit R g 1))

theorem rowMagic_relations {s} (R : Rows s) (g : Fin (RowSlots.squares R)) :
    PauliExtraction.SquareRelations 1 (rowMagic R g) := by
  apply magicCells_relations
  apply scalar_pauli
  intro he
  have hh := congrArg Fin.val he
  simp only [squareBit,Fin.val_zero,Fin.val_one] at hh
  omega

def axisBit {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) : Fin (bits R) :=
  squareBit R g ⟨k.val%2,Nat.mod_lt _ (by decide)⟩

def rowAxis {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) : Op :=
  if k.val<2 then scalarZ (bits R) (axisBit R g k) else scalarX (bits R) (axisBit R g k)

theorem rowAxis_star {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) :
    star (rowAxis R g k)=rowAxis R g k := by
  by_cases hk : k.val<2
  · simpa only [rowAxis,ite_eq_left hk] using scalarZ_star (bits R) (axisBit R g k)
  · simpa only [rowAxis,ite_eq_right hk] using scalarX_star (bits R) (axisBit R g k)

theorem rowAxis_square {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) :
    rowAxis R g k*rowAxis R g k=1 := by
  by_cases hk : k.val<2
  · simpa only [rowAxis,ite_eq_left hk] using scalarZ_square (bits R) (axisBit R g k)
  · simpa only [rowAxis,ite_eq_right hk] using scalarX_square (bits R) (axisBit R g k)

theorem rowAxis_amplify {s} (R : Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) (E : Op) :
    Commute (amplify (RowSlots.dimension R) E) (rowAxis R g k) := by
  simp only [RowScalar.dimension_bits]
  by_cases hk : k.val<2
  · simpa only [rowAxis,ite_eq_left hk] using scalarZ_amplify (bits R) (axisBit R g k) E
  · simpa only [rowAxis,ite_eq_right hk] using scalarX_amplify (bits R) (axisBit R g k) E

theorem crossAxis_commute {s} (R : Rows s) (g h : Fin (RowSlots.squares R)) (hgh : g≠h)
    (k l : Fin 4) : Commute (rowAxis R g k) (rowAxis R h l) := by
  have hne : axisBit R g k≠axisBit R h l := by
    intro he
    have hv := congrArg Fin.val he
    have hk := Nat.mod_lt k.val (by decide : 0<2)
    have hl := Nat.mod_lt l.val (by decide : 0<2)
    have hh : g.val=h.val := by simpa only [axisBit,squareBit] using (show g.val=h.val from by
      dsimp [axisBit,squareBit] at hv
      omega)
    exact hgh (Fin.ext hh)
  unfold rowAxis
  split_ifs
  · exact scalarZ_commute _ _ _
  · exact (scalarXZ_commute _ _ _ (Ne.symm hne)).symm
  · exact scalarXZ_commute _ _ _ hne
  · exact scalarX_commute _ _ _

theorem amplify_projection (d : ℕ) [NeZero d] (E : Op) (hE : Projection E) :
    Projection (amplify d E) := by
  constructor
  · rw [← amplify_star,hE.1]
  · rw [← amplify_mul,hE.2]

/-- The honest old-axis joint, retaining the old event's positive bit. -/
def oldAxisPartition (E U : Op) (hE : Projection E) (hs : star U=U) (hq : U*U=1)
    (hc : Commute E U) : Partition Op (Bool × Bool) :=
  (Partition.binary E hE.1 hE.2).joint (Partition.reflection U hs hq) (by
    intro b c
    have he : Commute E ((1/2:ℂ) • (1+sign c • U)) :=
      ((Commute.one_right E).add_right (hc.smul_right (sign c))).smul_right (1/2:ℂ)
    cases b
    · exact ((Commute.one_left _).sub_left he).eq
    · exact he.eq)


def honestColumnPartition {s} (R : Rows s) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (r : Fin R.rowCount) : Partition Op (Fin (RowSlots.dimension R)) where
  effect a := columnEffect R E r a
  selfadjoint a := (columnEffect_projection R E hE r a).1
  product a b := by
    by_cases h : a=b
    · subst b; rw [if_pos rfl]; exact (columnEffect_projection R E hE r a).2
    · rw [if_neg h]; exact columnEffect_orthogonal R E hE r a b h
  total := columnEffect_sum R E hE r

/-- Every new question is assigned a complete l2 projective POVM, simultaneously.
The scalar pair and slot families use the same register as the old amplifications. -/
def slotEvent {s} (R : Rows s) (E : Fin R.count → Op) (r : Fin R.rowCount) (j : ℕ) : Op :=
  match (RowSlots.slot R r j).event with | none => 1 | some i => E i

theorem slotEvent_projection {s} (R : Rows s) (E : Fin R.count → Op) (hE : ∀ i,Projection (E i))
    (r : Fin R.rowCount) (j : ℕ) : Projection (slotEvent R E r j) := by
  unfold slotEvent
  cases (RowSlots.slot R r j).event
  · exact ⟨by simp,by simp⟩
  · exact hE _

def newPartition (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (q : Q R) : Partition Op (AA (scenario G R)) := by
  let N := (scenario G R).answersA+1
  have hd : 2^(bits R)=RowSlots.dimension R := (RowScalar.dimension_bits R).symm
  have hN : 2*RowSlots.dimension R+6<N := by dsimp [N,scenario]; omega
  have pad2 (a : Bool) : bitAnswer a<N := by cases a <;> simp [bitAnswer] <;> omega
  have pad4 (a : Bool × Bool) : 2*bit a.1+bit a.2<N := by
    have := bit_lt a.1; have := bit_lt a.2; omega
  have pad4' (a : Bool × Bool) : 2*bitAnswer a.1+bitAnswer a.2<N := by
    cases a.1 <;> cases a.2 <;> simp [bitAnswer] <;> omega
  cases q with
  | anchor => exact Partition.deterministic ⟨1,by omega⟩
  | cell g x y =>
      let hr := rowMagic_relations R g
      exact padPartition (Partition.reflection (rowMagic R g x y) (hr.selfadjoint x y) (hr.square x y))
        N bitAnswer pad2
  | line g col k =>
      let hr := rowMagic_relations R g
      let U := if col then rowMagic R g 0 k else rowMagic R g k 0
      let V := if col then rowMagic R g 1 k else rowMagic R g k 1
      have hsU : star U=U := by
        cases col
        · exact hr.selfadjoint k 0
        · exact hr.selfadjoint 0 k
      have hsV : star V=V := by
        cases col
        · exact hr.selfadjoint k 1
        · exact hr.selfadjoint 1 k
      have hqU : U*U=1 := by
        cases col
        · exact hr.square k 0
        · exact hr.square 0 k
      have hqV : V*V=1 := by
        cases col
        · exact hr.square k 1
        · exact hr.square 1 k
      have hc : U*V=V*U := by
        cases col
        · exact hr.row_commute k 0 1
        · exact hr.col_commute 0 1 k
      exact padPartition (linePartition U V hsU hsV hqU hqV hc) N (fun a => 2*bit a.1+bit a.2) pad4
  | cross g h k l =>
      by_cases hgh : g=h
      · exact Partition.deterministic ⟨0,by omega⟩
      · exact padPartition (linePartition (rowAxis R g k) (rowAxis R h l)
          (rowAxis_star R g k) (rowAxis_star R h l) (rowAxis_square R g k) (rowAxis_square R h l)
          (crossAxis_commute R g h hgh k l).eq) N
          (fun a => 2*bitAnswer a.1+bitAnswer a.2) pad4'
  | oldAxis i g k =>
      let A := amplify (RowSlots.dimension R) (E i)
      exact padPartition (oldAxisPartition A (rowAxis R g k) (amplify_projection (RowSlots.dimension R) (E i) (hE i))
        (rowAxis_star R g k) (rowAxis_square R g k) (rowAxis_amplify R g k (E i)))
        N (fun a => 2*bit a.1+bitAnswer a.2) (by
          intro a; have := bit_lt a.1; cases a.2 <;> simp [bitAnswer] <;> omega)
  | global isX =>
      cases isX
      · exact padPartition (realizePartition (diagonalPartition (2^(bits R)))) N Fin.val (by intro a; have := a.isLt; omega)
      · exact padPartition (realizePartition (fourierPartition (bits R))) N Fin.val (by intro a; have := a.isLt; omega)
  | pair j =>
      by_cases hj : j<2^(bits R)
      · exact padPartition (realizePartition (pairPartition (bits R) j hj)) N
          (fun a => 2*a.2.val+bit a.1) (by intro a; have := a.2.isLt; have := bit_lt a.1; omega)
      · exact Partition.deterministic ⟨0,by omega⟩
  | slot r j =>
      by_cases hj : j<2^(bits R)
      · exact padPartition (realizePartition (slotPartition (bits R) j hj
          (slotEvent R E r j) (slotEvent_projection R E hE r j))) N
          (fun a => 3*bit a.1+a.2.val) (by intro a; have := bit_lt a.1; have := a.2.isLt; omega)
      · exact Partition.deterministic ⟨0,by omega⟩
  | column r =>
      exact padPartition (honestColumnPartition R E hE r) N Fin.val (by intro a; have := a.isLt; omega)

private theorem deterministic_invalid {N : ℕ} (v a : Fin N) (valid : ℕ → Bool)
    (hv : valid v.val=true) (ha : valid a.val=false) :
    (Partition.deterministic (A:=Op) v).effect a=0 := by
  change (if a=v then (1:Op) else 0)=0
  by_cases h : a=v
  · subst a; rw [hv] at ha; contradiction
  · simp [h]

/-- Invalid fine answers have literal zero operators in the simultaneous family. -/
theorem newPartition_invalid (G : Game) (R : Rows G.scenario) (E : Fin R.count → Op)
    (hE : ∀ i,Projection (E i)) (q : Q R) (a : AA (scenario G R))
    (ha : valid R q a.val=false) : (newPartition G R E hE q).effect a=0 := by
  have hd : 2^(bits R)=RowSlots.dimension R := (RowScalar.dimension_bits R).symm
  have hdpos := RowSlots.dimension_pos R
  cases q with
  | anchor =>
      apply deterministic_invalid _ a (valid R .anchor) (by simp [valid]) ha
  | cell g x y =>
      apply padPartition_invalid (valid:=valid R (.cell g x y)) (ha:=ha)
      intro b
      cases b <;> simp [valid,bitAnswer]
  | line g col k =>
      apply padPartition_invalid (valid:=valid R (.line g col k)) (ha:=ha)
      intro b
      simp only [valid,decide_eq_true_eq]
      have := bit_lt b.1; have := bit_lt b.2
      omega
  | cross g h k l =>
      dsimp only [newPartition]
      split_ifs with hgh
      · apply deterministic_invalid _ a (valid R (.cross g h k l)) (by simp [valid,hgh]) ha
      · apply padPartition_invalid (valid:=valid R (.cross g h k l)) (ha:=ha)
        intro b
        cases b.1 <;> cases b.2 <;> simp [valid,hgh,bitAnswer]
  | oldAxis i g k =>
      apply padPartition_invalid (valid:=valid R (.oldAxis i g k)) (ha:=ha)
      intro b
      have := bit_lt b.1
      cases b.2 <;> simp [valid,bitAnswer] <;> omega
  | global isX =>
      cases isX
      all_goals apply padPartition_invalid (valid:=valid R (.global _)) (ha:=ha)
      all_goals intro b; simp only [valid,decide_eq_true_eq]; have := b.isLt; omega
  | pair j =>
      dsimp only [newPartition]
      split_ifs with hj
      · apply padPartition_invalid_on_support (valid:=valid R (.pair j)) (ha:=ha)
        intro b hb
        have hcanonical : ¬b.2.val ≤ Nat.xor b.2.val j := by
          intro hc
          have hn : 2*b.2.val+bit b.1<2*RowSlots.dimension R := by
            have := b.2.isLt; have := bit_lt b.1; omega
          have hdiv : (2*b.2.val+bit b.1)/2=b.2.val := by have := bit_lt b.1; omega
          have hv : valid R (.pair j) (2*b.2.val+bit b.1)=true := by
            simp only [valid,decide_eq_true_eq,hdiv]
            exact ⟨hn,hc⟩
          rw [hv] at hb
          contradiction
        change matrixOp _ ((pairPartition (bits R) j hj).effect b)=0
        rw [pair_noncanonical _ _ _ b hcanonical,matrixOp_zero]
      · apply deterministic_invalid _ a (valid R (.pair j)) ?_ ha
        simp [valid,hdpos,Nat.xor_eq]
  | slot r j =>
      dsimp only [newPartition]
      split_ifs with hj
      · apply padPartition_invalid (valid:=valid R (.slot r j)) (ha:=ha)
        intro b
        simp only [valid,decide_eq_true_eq]
        have := bit_lt b.1; have := b.2.isLt
        omega
      · apply deterministic_invalid _ a (valid R (.slot r j)) (by simp [valid]) ha
  | column r =>
      apply padPartition_invalid (valid:=valid R (.column r)) (ha:=ha)
      intro b
      simpa only [valid,decide_eq_true_eq] using b.isLt

/-- The simultaneous family together with every unchanged, padded old POVM. -/
def honestMeasurements (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) :
    Measurements (scenario G R) :=
  assembleMeasurements G R M (fun q => (newPartition G R E hE q).toPOVM)
    (fun q => (newPartition G R F hF q).toPOVM)

theorem honestMeasurements_oldA (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (x a) :
    (honestMeasurements G R M E F hE hF).alice ((embedding G R).qA x) ((embedding G R).aA a)=
      amplify (RowSlots.dimension R) (M.alice x a) :=
  assembleMeasurements_oldA G R M _ _ x a

theorem honestMeasurements_oldB (G : Game) (R : Rows G.scenario) (M : Measurements G.scenario)
    (E F : Fin R.count → Op) (hE : ∀ i,Projection (E i)) (hF : ∀ i,Projection (F i)) (y b) :
    (honestMeasurements G R M E F hE hF).bob ((embedding G R).qB y) ((embedding G R).aB b)=
      amplify (RowSlots.dimension R) (M.bob y b) :=
  assembleMeasurements_oldB G R M _ _ y b

end Sigma2.RowCompleteness
