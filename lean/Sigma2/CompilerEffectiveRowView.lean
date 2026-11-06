import Sigma2.CompilerEffectiveRowSlots
import Sigma2.CompilerEffectivePreAccept
noncomputable section
set_option maxHeartbeats 250000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective
set_option allowUnsafeReducibility true in
attribute [local reducible] CompilerScaffold.rows
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList encodingCount refinementCount scenario RowSlots.raw RowSlots.bound RowSlots.squares RowSlots.dimension RowSlots.slots RowSlots.slot RowGame.questions RowGame.axis
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.cond

abbrev RowQuestionData := ℕ × ℕ × ℕ × ℕ × ℕ × Bool

def vAnchor : RowQuestionData := (0,0,0,0,0,false)
def vCell (g x y : ℕ) : RowQuestionData := (1,g,x,y,0,false)
def vLine (g : ℕ) (col : Bool) (k : ℕ) : RowQuestionData := (2,g,k,0,0,col)
def vCross (g h k l : ℕ) : RowQuestionData := (3,g,h,k,l,false)
def vOldAxis (i g k : ℕ) : RowQuestionData := (4,i,g,k,0,false)
def vGlobal (isX : Bool) : RowQuestionData := (5,0,0,0,0,isX)
def vPair (j : ℕ) : RowQuestionData := (6,j,0,0,0,false)
def vSlot (r j : ℕ) : RowQuestionData := (7,r,j,0,0,false)
def vColumn (r : ℕ) : RowQuestionData := (8,r,0,0,0,false)

def rowView {n m r : ℕ} : RowGame.Question n m r → RowQuestionData
  | .anchor => vAnchor
  | .cell g x y => vCell g.val x.val y.val
  | .line g col k => vLine g.val col k.val
  | .cross g h k l => vCross g.val h.val k.val l.val
  | .oldAxis i g k => vOldAxis i.val g.val k.val
  | .global isX => vGlobal isX
  | .pair j => vPair j
  | .slot r j => vSlot r.val j
  | .column r => vColumn r.val

theorem rowView_injective {n m r : ℕ} : Function.Injective (@rowView n m r) := by
  intro q p h
  cases q <;> cases p <;>
    simp_all only [rowView,vAnchor,vCell,vLine,vCross,vOldAxis,vGlobal,vPair,vSlot,vColumn,Prod.mk.injEq,Fin.ext_iff,reduceCtorEq,Nat.reduceEqDiff,and_true,true_and,and_false,false_and,RowGame.Question.cell.injEq,RowGame.Question.line.injEq,RowGame.Question.cross.injEq,RowGame.Question.oldAxis.injEq,RowGame.Question.global.injEq,RowGame.Question.pair.injEq,RowGame.Question.slot.injEq,RowGame.Question.column.injEq]
@[simp] theorem rowView_inj {n m r : ℕ} (q p : RowGame.Question n m r) :
    rowView q=rowView p ↔ q=p := rowView_injective.eq_iff

variable {α : Type} [Primcodable α]
@[fun_prop] theorem cvCell (g x y : α → ℕ) (hg : Computable g) (hx : Computable x) (hy : Computable y) :
    Computable (fun a => vCell (g a) (x a) (y a)) := by unfold vCell; fun_prop
@[fun_prop] theorem cvLine (g : α → ℕ) (c : α → Bool) (k : α → ℕ)
    (hg : Computable g) (hc : Computable c) (hk : Computable k) :
    Computable (fun a => vLine (g a) (c a) (k a)) := by unfold vLine; fun_prop
@[fun_prop] theorem cvCross (g h k l : α → ℕ)
    (hg : Computable g) (hh : Computable h) (hk : Computable k) (hl : Computable l) :
    Computable (fun a => vCross (g a) (h a) (k a) (l a)) := by unfold vCross; fun_prop
@[fun_prop] theorem cvOldAxis (i g k : α → ℕ) (hi : Computable i) (hg : Computable g) (hk : Computable k) :
    Computable (fun a => vOldAxis (i a) (g a) (k a)) := by unfold vOldAxis; fun_prop
@[fun_prop] theorem cvGlobal (b : α → Bool) (hb : Computable b) :
    Computable (fun a => vGlobal (b a)) := by unfold vGlobal; fun_prop
@[fun_prop] theorem cvPair (j : α → ℕ) (hj : Computable j) :
    Computable (fun a => vPair (j a)) := by unfold vPair; fun_prop
@[fun_prop] theorem cvSlot (r j : α → ℕ) (hr : Computable r) (hj : Computable j) :
    Computable (fun a => vSlot (r a) (j a)) := by unfold vSlot; fun_prop
@[fun_prop] theorem cvColumn (r : α → ℕ) (hr : Computable r) :
    Computable (fun a => vColumn (r a)) := by unfold vColumn; fun_prop

def axisView (g k : ℕ) : RowQuestionData :=
  if k=0 then vCell g 0 0 else if k=1 then vCell g 1 0
  else if k=2 then vCell g 1 1 else vCell g 0 1
@[fun_prop] theorem caxisView (g k : α → ℕ) (hg : Computable g) (hk : Computable k) :
    Computable (fun a => axisView (g a) (k a)) := by unfold axisView; fun_prop

theorem axisView_eq {s} (R : Compiler.Rows s) (g : Fin (RowSlots.squares R)) (k : Fin 4) :
    axisView g.val k.val=rowView (RowGame.axis R g k) := by
  have h0 : k=0 ↔ k.val=0 := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  have h1 : k=1 ↔ k.val=1 := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  have h2 : k=2 ↔ k.val=2 := ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  unfold axisView RowGame.axis
  simp only [h0,h1,h2]
  split_ifs <;> rfl

def questionsNat (P : Presentation) : List RowQuestionData :=
  [vAnchor] ++
  (List.range (squaresNat P)).flatMap (fun g =>
    (List.range 3).flatMap (fun x => (List.range 3).map (fun y => vCell g x y))) ++
  (List.range (squaresNat P)).flatMap (fun g =>
    [false,true].flatMap (fun col => (List.range 3).map (fun k => vLine g col k))) ++
  (List.range (squaresNat P)).flatMap (fun g => (List.range (squaresNat P)).flatMap (fun h =>
    (List.range 4).flatMap (fun k => (List.range 4).map (fun l => vCross g h k l)))) ++
  (List.range (names P).length).flatMap (fun i => (List.range (squaresNat P)).flatMap (fun g =>
    (List.range 4).map (fun k => vOldAxis i g k))) ++
  [vGlobal false,vGlobal true] ++
  ((List.range (dimensionNat P)).drop 1).map vPair ++
  (List.range (rowList P).length).flatMap (fun r =>
    ((List.range (dimensionNat P)).drop 1).map (vSlot r)) ++
  (List.range (rowList P).length).map vColumn
attribute [local irreducible] questionsNat

set_option maxHeartbeats 1000000 in
@[fun_prop] theorem cquestionsNat (P : α → Presentation) (hP : Computable P) :
    Computable (fun a => questionsNat (P a)) := by
  have hs := csquaresNat P hP
  have hd := cdimensionNat P hP
  have hn := clen _ (names_computable.comp hP)
  have hm := clen _ (rowList_computable.comp hP)
  have hcellY : Computable (fun z : ((α × ℕ) × ℕ) × ℕ => vCell z.1.1.2 z.1.2 z.2) := by fun_prop
  have hcellX : Computable (fun z : (α × ℕ) × ℕ => (List.range 3).map (fun y => vCell z.1.2 z.2 y)) :=
    cmap _ _ (Computable.const _) hcellY
  have hcellG : Computable (fun z : α × ℕ => (List.range 3).flatMap (fun x => (List.range 3).map (fun y => vCell z.2 x y))) :=
    cflat _ _ (Computable.const _) hcellX
  have hcells := cflat _ _ (crange _ hs) hcellG
  have hlineK : Computable (fun z : ((α × ℕ) × Bool) × ℕ => vLine z.1.1.2 z.1.2 z.2) := by fun_prop
  have hlineCol : Computable (fun z : (α × ℕ) × Bool => (List.range 3).map (fun k => vLine z.1.2 z.2 k)) :=
    cmap _ _ (Computable.const _) hlineK
  have hlineG : Computable (fun z : α × ℕ => [false,true].flatMap (fun col => (List.range 3).map (fun k => vLine z.2 col k))) :=
    cflat _ _ (Computable.const _) hlineCol
  have hlines := cflat _ _ (crange _ hs) hlineG
  have hcrossL : Computable (fun z : (((α × ℕ) × ℕ) × ℕ) × ℕ => vCross z.1.1.1.2 z.1.1.2 z.1.2 z.2) := by fun_prop
  have hcrossK : Computable (fun z : ((α × ℕ) × ℕ) × ℕ => (List.range 4).map (fun l => vCross z.1.1.2 z.1.2 z.2 l)) :=
    cmap _ _ (Computable.const _) hcrossL
  have hcrossH : Computable (fun z : (α × ℕ) × ℕ => (List.range 4).flatMap (fun k => (List.range 4).map (fun l => vCross z.1.2 z.2 k l))) :=
    cflat _ _ (Computable.const _) hcrossK
  have hcrossG : Computable (fun z : α × ℕ => (List.range (squaresNat (P z.1))).flatMap (fun h =>
      (List.range 4).flatMap (fun k => (List.range 4).map (fun l => vCross z.2 h k l)))) :=
    cflat _ _ (crange _ (hs.comp Computable.fst)) hcrossH
  have hcross := cflat _ _ (crange _ hs) hcrossG
  have holdK : Computable (fun z : ((α × ℕ) × ℕ) × ℕ => vOldAxis z.1.1.2 z.1.2 z.2) := by fun_prop
  have holdG : Computable (fun z : (α × ℕ) × ℕ => (List.range 4).map (fun k => vOldAxis z.1.2 z.2 k)) :=
    cmap _ _ (Computable.const _) holdK
  have holdI : Computable (fun z : α × ℕ => (List.range (squaresNat (P z.1))).flatMap (fun g =>
      (List.range 4).map (fun k => vOldAxis z.2 g k))) :=
    cflat _ _ (crange _ (hs.comp Computable.fst)) holdG
  have holds := cflat _ _ (crange _ hn) holdI
  have hj := cdrop (fun _ : α => 1) (fun a => List.range (dimensionNat (P a))) (Computable.const 1) (crange _ hd)
  have hpairs := cmap _ (fun z : α × ℕ => vPair z.2) hj (by fun_prop)
  have hslotJ : Computable (fun z : (α × ℕ) × ℕ => vSlot z.1.2 z.2) := by fun_prop
  have hslotR : Computable (fun z : α × ℕ => ((List.range (dimensionNat (P z.1))).drop 1).map (fun j => vSlot z.2 j)) :=
    cmap _ _ (hj.comp Computable.fst) hslotJ
  have hslots := cflat _ _ (crange _ hm) hslotR
  have hcolumns := cmap _ (fun z : α × ℕ => vColumn z.2) (crange _ hm) (by fun_prop)
  have hc := capp _ _ (capp _ _ (capp _ _ (capp _ _ (capp _ _ (capp _ _ (capp _ _ (capp _ _
    (Computable.const [vAnchor]) hcells) hlines) hcross) holds)
      (Computable.const [vGlobal false,vGlobal true])) hpairs) hslots) hcolumns
  exact hc.of_eq (fun a => by unfold questionsNat; rfl)

theorem finRange_map_eq {σ : Type} {n : ℕ} (f : Fin n → σ) (g : ℕ → σ) (h : ∀ i, f i=g i.val) :
    (List.finRange n).map f=(List.range n).map g := by
  rw [← List.ofFn_eq_map]
  exact ofFn_eq_range f g h

theorem finRange_values (n : ℕ) : (List.finRange n).map Fin.val=List.range n := by
  simpa using finRange_map_eq (fun i : Fin n => i.val) id (fun _ => rfl)

theorem finRange_flat_eq {σ : Type} {n : ℕ} (f : Fin n → List σ) (g : ℕ → List σ) (h : ∀ i, f i=g i.val) :
    (List.finRange n).flatMap f=(List.range n).flatMap g := by
  rw [← finRange_values n,List.flatMap_map]
  congr 1
  funext i
  exact h i

theorem finRange_all_eq {n : ℕ} (f : Fin n → Bool) (g : ℕ → Bool) (h : ∀ i, f i=g i.val) :
    (List.finRange n).all f=(List.range n).all g := by
  rw [← finRange_values n,List.all_map]
  congr 1
  funext i
  exact h i

theorem questionsNat_eq (P : Presentation) : questionsNat P=(RowGame.questions (rows P)).map rowView := by
  symm
  unfold questionsNat RowGame.questions
  simp only [List.map_append,List.map_cons,List.map_nil,List.map_flatMap,List.map_map,Function.comp_def,rowView]
  conv_rhs => simp only [squaresNat_eq,dimensionNat_eq]
  repeat' first | apply congrArg₂ List.append | rfl
  · apply finRange_flat_eq
    intro g
    apply finRange_flat_eq
    intro x
    exact finRange_map_eq _ _ (fun _ => rfl)
  · apply finRange_flat_eq
    intro g
    apply congrArg (fun f : Bool → List RowQuestionData => [false,true].flatMap f)
    funext col
    exact finRange_map_eq _ _ (fun _ => rfl)
  · apply finRange_flat_eq
    intro g
    apply finRange_flat_eq
    intro h
    apply finRange_flat_eq
    intro k
    exact finRange_map_eq _ _ (fun _ => rfl)
  · apply finRange_flat_eq
    intro i
    apply finRange_flat_eq
    intro g
    exact finRange_map_eq _ _ (fun _ => rfl)
  · apply finRange_flat_eq
    intro r
    rfl
  · exact finRange_map_eq _ _ (fun _ => rfl)

#print axioms rowView_injective
#print axioms cquestionsNat
#print axioms questionsNat_eq
end Sigma2.CompilerEffectiveCoding