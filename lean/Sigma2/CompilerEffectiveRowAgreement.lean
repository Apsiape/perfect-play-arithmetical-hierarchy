import Sigma2.CompilerEffectiveRowRules
noncomputable section
set_option maxHeartbeats 250000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective Compiler
set_option allowUnsafeReducibility true in
attribute [local reducible] CompilerScaffold.rows CompilerScaffold.preGame RowGame.scenario
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList encodingCount
  refinementCount scenario RowSlots.raw RowSlots.bound RowSlots.squares RowSlots.dimension
  RowSlots.slots RowSlots.slot RowGame.questions RowGame.axis RowGame.valid
  validRowNat directedRowNat newRuleNat bindOldANat bindOldBNat oldSyncNat
  questionLookupNat decodeRowNat acceptsRowNat questionsNat slotNat

lemma decideIff_any (p q : Prop) [Decidable p] [Decidable q] (d : Decidable (p ↔ q)) :
    @decide (p ↔ q) d=(decide p == decide q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]

@[simp] theorem rowView_anchor_eq {n m r : ℕ} (p : RowGame.Question n m r) :
    rowView p=vAnchor ↔ p=.anchor := rowView_inj p .anchor
@[simp] theorem rowView_cell_eq {n m r : ℕ} (p : RowGame.Question n m r) (g : Fin r) (x y : Fin 3) :
    rowView p=vCell g.val x.val y.val ↔ p=.cell g x y := rowView_inj p (.cell g x y)
@[simp] theorem rowView_line_eq {n m r : ℕ} (p : RowGame.Question n m r) (g : Fin r) (c : Bool) (k : Fin 3) :
    rowView p=vLine g.val c k.val ↔ p=.line g c k := rowView_inj p (.line g c k)
@[simp] theorem rowView_cross_eq {n m r : ℕ} (p : RowGame.Question n m r) (g h : Fin r) (k l : Fin 4) :
    rowView p=vCross g.val h.val k.val l.val ↔ p=.cross g h k l := rowView_inj p (.cross g h k l)
@[simp] theorem rowView_oldAxis_eq {n m r : ℕ} (p : RowGame.Question n m r) (i : Fin n) (g : Fin r) (k : Fin 4) :
    rowView p=vOldAxis i.val g.val k.val ↔ p=.oldAxis i g k := rowView_inj p (.oldAxis i g k)
@[simp] theorem rowView_global_eq {n m r : ℕ} (p : RowGame.Question n m r) (b : Bool) :
    rowView p=vGlobal b ↔ p=.global b := rowView_inj p (.global b)
@[simp] theorem rowView_pair_eq {n m r : ℕ} (p : RowGame.Question n m r) (j : ℕ) :
    rowView p=vPair j ↔ p=.pair j := rowView_inj p (.pair j)
@[simp] theorem rowView_slot_eq {n m r : ℕ} (p : RowGame.Question n m r) (s : Fin m) (j : ℕ) :
    rowView p=vSlot s.val j ↔ p=.slot s j := rowView_inj p (.slot s j)
@[simp] theorem rowView_column_eq {n m r : ℕ} (p : RowGame.Question n m r) (s : Fin m) :
    rowView p=vColumn s.val ↔ p=.column s := rowView_inj p (.column s)

theorem validRowNat_eq (P : Presentation) (q : RowGame.Q (rows P)) (a : ℕ) :
    validRowNat P (rowView q) a=RowGame.valid (rows P) q a := by
  cases q <;> simp [validRowNat,rowView,vAnchor,vCell,vLine,vCross,vOldAxis,vGlobal,vPair,vSlot,vColumn,
    RowGame.valid,dimensionNat_eq,Fin.ext_iff,decideIff_any]

theorem slotEventNat_eq (P : Presentation) (r : Fin (rowList P).length) (j : ℕ) :
    (slotNat P r.val j).1=(RowSlots.slot (rows P) r j).event.map Fin.val :=
  congrArg Prod.fst (slotNat_eq P r j)
theorem slotNegativeNat_eq (P : Presentation) (r : Fin (rowList P).length) (j : ℕ) :
    (slotNat P r.val j).2=(RowSlots.slot (rows P) r j).negative :=
  congrArg Prod.snd (slotNat_eq P r j)

theorem oldSyncNat_eq (P : Presentation) (x : QA (scenario P)) (y : QB (scenario P)) (a b : ℕ) :
    oldSyncNat P x.val y.val a b=RowGame.oldSync (rows P) x y a b := by
  unfold oldSyncNat RowGame.oldSync
  symm
  apply finRange_all_eq
  intro i
  by_cases hx : x.val=i.val <;> by_cases hy : y.val=i.val <;>
    by_cases ha : a=1 <;> by_cases hb : b=1 <;>
      simp [CompilerScaffold.rows,CompilerScaffold.event,Fin.ext_iff,hx,hy,ha,hb]

theorem bindOldANat_eq (P : Presentation) (x : QA (scenario P)) (q : RowGame.Q (rows P)) (a b : ℕ) :
    bindOldANat P x.val (rowView q) a b=RowGame.bindOldA (rows P) x q a b := by
  cases q with
  | anchor => simp [bindOldANat,rowView,vAnchor,RowGame.bindOldA]
  | cell g u v => simp [bindOldANat,rowView,vCell,RowGame.bindOldA]
  | line g c k => simp [bindOldANat,rowView,vLine,RowGame.bindOldA]
  | cross g h k l => simp [bindOldANat,rowView,vCross,RowGame.bindOldA]
  | oldAxis i g k =>
    by_cases hx : x.val=i.val <;> by_cases ha : a=1 <;> by_cases hb : b/2=1 <;>
      simp [bindOldANat,rowView,vOldAxis,RowGame.bindOldA,CompilerScaffold.rows,CompilerScaffold.event,Fin.ext_iff,hx,ha,hb]
  | global b => simp [bindOldANat,rowView,vGlobal,RowGame.bindOldA]
  | pair j => simp [bindOldANat,rowView,vPair,RowGame.bindOldA]
  | slot r j =>
    cases h : (RowSlots.slot (rows P) r j).event with
    | none => simp [bindOldANat,rowView,vSlot,RowGame.bindOldA,slotEventNat_eq,h]
    | some i =>
      by_cases hx : x.val=i.val <;> by_cases ha : a=1 <;> by_cases hb : b/3=1 <;>
        simp [bindOldANat,rowView,vSlot,RowGame.bindOldA,slotEventNat_eq,h,CompilerScaffold.rows,CompilerScaffold.event,Fin.ext_iff,hx,ha,hb]
  | column r => simp [bindOldANat,rowView,vColumn,RowGame.bindOldA]

theorem bindOldBNat_eq (P : Presentation) (q : RowGame.Q (rows P)) (y : QB (scenario P)) (a b : ℕ) :
    bindOldBNat P (rowView q) y.val a b=RowGame.bindOldB (rows P) q y a b := by
  cases q with
  | anchor => simp [bindOldBNat,rowView,vAnchor,RowGame.bindOldB]
  | cell g u v => simp [bindOldBNat,rowView,vCell,RowGame.bindOldB]
  | line g c k => simp [bindOldBNat,rowView,vLine,RowGame.bindOldB]
  | cross g h k l => simp [bindOldBNat,rowView,vCross,RowGame.bindOldB]
  | oldAxis i g k =>
    by_cases hy : y.val=i.val <;> by_cases hb : b=1 <;> by_cases ha : a/2=1 <;>
      simp [bindOldBNat,rowView,vOldAxis,RowGame.bindOldB,CompilerScaffold.rows,CompilerScaffold.event,Fin.ext_iff,hy,ha,hb]
  | global b => simp [bindOldBNat,rowView,vGlobal,RowGame.bindOldB]
  | pair j => simp [bindOldBNat,rowView,vPair,RowGame.bindOldB]
  | slot r j =>
    cases h : (RowSlots.slot (rows P) r j).event with
    | none => simp [bindOldBNat,rowView,vSlot,RowGame.bindOldB,slotEventNat_eq,h]
    | some i =>
      by_cases hy : y.val=i.val <;> by_cases hb : b=1 <;> by_cases ha : a/3=1 <;>
        simp [bindOldBNat,rowView,vSlot,RowGame.bindOldB,slotEventNat_eq,h,CompilerScaffold.rows,CompilerScaffold.event,Fin.ext_iff,hy,ha,hb]
  | column r => simp [bindOldBNat,rowView,vColumn,RowGame.bindOldB]
theorem questionLookup_eq (P : Presentation) (k : ℕ) :
    (questionsNat P)[k]?.getD vAnchor =
      rowView ((RowGame.questions (rows P))[k]?.getD .anchor) := by
  rw [questionsNat_eq]
  cases h : (RowGame.questions (rows P))[k]? <;> simp [h,rowView]

theorem pre_counts_eq (P : Presentation) : (scenario P).questionsB=(scenario P).questionsA := by
  unfold CompilerScaffold.scenario
  rfl

theorem decodeRowNat_eqA (P : Presentation) (x : QA (RowGame.scenario (preGame P) (rows P))) :
    decodeRowNat P x.val=Sum.map (fun y : QA (scenario P) => y.val) rowView
      (RowGame.decodeA (preGame P) (rows P) x) := by
  unfold decodeRowNat RowGame.decodeA
  by_cases hx : x.val<(scenario P).questionsA+1
  · have hx' : x.val<(preGame P).scenario.questionsA+1 := hx
    rw [ite_eq_left hx,dif_pos hx']
    rfl
  · have hx' : ¬x.val<(preGame P).scenario.questionsA+1 := hx
    rw [ite_eq_right hx,dif_neg hx']
    simp only [Sum.map]
    apply congrArg Sum.inr
    unfold questionLookupNat
    exact questionLookup_eq P _
theorem decodeRowNat_eqB (P : Presentation) (y : QB (RowGame.scenario (preGame P) (rows P))) :
    decodeRowNat P y.val=Sum.map (fun x : QB (scenario P) => x.val) rowView
      (RowGame.decodeB (preGame P) (rows P) y) := by
  have hbound : (preGame P).scenario.questionsB+1=(scenario P).questionsA+1 :=
    congrArg (fun n : ℕ => n+1) (pre_counts_eq P)
  have hcond : (y.val<(preGame P).scenario.questionsB+1) ↔ (y.val<(scenario P).questionsA+1) :=
    Iff.of_eq (congrArg (fun n : ℕ => y.val<n) hbound)
  have hoff : y.val-((preGame P).scenario.questionsB+1)=y.val-((scenario P).questionsA+1) :=
    congrArg (fun n : ℕ => y.val-n) hbound
  unfold decodeRowNat RowGame.decodeB
  by_cases hy : y.val<(scenario P).questionsA+1
  · rw [ite_eq_left hy,dif_pos (hcond.mpr hy)]
    rfl
  · have hy' : ¬y.val<(preGame P).scenario.questionsB+1 := fun h => hy (hcond.mp h)
    rw [ite_eq_right hy,dif_neg hy']
    simp only [Sum.map]
    apply congrArg Sum.inr
    unfold questionLookupNat
    calc
      _ = rowView ((RowGame.questions (rows P))[y.val-((scenario P).questionsA+1)]?.getD .anchor) := questionLookup_eq P _
      _ = _ := congrArg (fun k : ℕ => rowView ((RowGame.questions (rows P))[k]?.getD .anchor)) hoff.symm
#print axioms validRowNat_eq
#print axioms oldSyncNat_eq
#print axioms bindOldANat_eq
#print axioms bindOldBNat_eq
#print axioms decodeRowNat_eqA
#print axioms decodeRowNat_eqB
end Sigma2.CompilerEffectiveCoding