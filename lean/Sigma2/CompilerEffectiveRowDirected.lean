import Sigma2.CompilerEffectiveRowAgreement
noncomputable section
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective Compiler
set_option allowUnsafeReducibility true in
attribute [local reducible] CompilerScaffold.rows
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList encodingCount
  refinementCount scenario RowSlots.raw RowSlots.bound RowSlots.squares RowSlots.dimension
  RowSlots.slots RowSlots.slot RowGame.questions RowGame.axis RowGame.valid RowGame.directed
  Compiler.cellSign RowGame.parity RowGame.scalarClass RowGame.bitAnswer
  validRowNat directedRowNat newRuleNat bindOldANat bindOldBNat oldSyncNat
  questionLookupNat decodeRowNat acceptsRowNat questionsNat slotNat

theorem directedRowNat_eq (P : Presentation) (q p : RowGame.Q (rows P)) (a b : ℕ) :
    directedRowNat P (rowView q) (rowView p) a b=RowGame.directed (rows P) q p a b := by
  cases q with
  | anchor =>
    change directedRowNat P vAnchor (rowView p) a b=_
    simp [directedRowNat,vAnchor,RowGame.directed]
  | cell g x y =>
    change directedRowNat P (vCell g.val x.val y.val) (rowView p) a b=_
    simp [directedRowNat,vCell,RowGame.directed]
  | line g col k =>
    change directedRowNat P (vLine g.val col k.val) (rowView p) a b=_
    simp only [directedRowNat,vLine,RowGame.directed,Nat.reduceEqDiff,ite_true,ite_false]
    symm
    apply finRange_all_eq
    intro j
    cases col <;> simp
  | cross g h k l =>
    change directedRowNat P (vCross g.val h.val k.val l.val) (rowView p) a b=_
    have hg := axisView_eq (rows P) g k
    have hh := axisView_eq (rows P) h l
    simp [directedRowNat,vCross,RowGame.directed,hg,hh,Fin.ext_iff]
  | oldAxis i g k =>
    change directedRowNat P (vOldAxis i.val g.val k.val) (rowView p) a b=_
    have hg := axisView_eq (rows P) g k
    simp [directedRowNat,vOldAxis,RowGame.directed,hg]
  | global isX =>
    change directedRowNat P (vGlobal isX) (rowView p) a b=_
    simp only [directedRowNat,vGlobal,RowGame.directed,Nat.reduceEqDiff,ite_true,ite_false,squaresNat_eq]
    symm
    apply finRange_all_eq
    intro g
    apply finRange_all_eq
    intro k
    let ax : Fin 4 := ⟨k.val+if isX then 2 else 0,by split <;> omega⟩
    have hc : (rowView p=axisView g.val ax.val) ↔ p=RowGame.axis (rows P) g ax := by
      rw [axisView_eq (rows P) g ax,rowView_inj]
    change (if p=RowGame.axis (rows P) g ax then decide (b=RowGame.bitAnswer (Nat.testBit a (2*g.val+k.val))) else true)=
      (if rowView p=axisView g.val ax.val then decide (b=RowGame.bitAnswer (Nat.testBit a (2*g.val+k.val))) else true)
    simp only [hc]
  | pair j =>
    change directedRowNat P (vPair j) (rowView p) a b=_
    simp [directedRowNat,vPair,RowGame.directed,squaresNat_eq,dimensionNat_eq]
  | slot r j =>
    change directedRowNat P (vSlot r.val j) (rowView p) a b=_
    cases h : (RowSlots.slot (rows P) r j).event <;>
      simp [directedRowNat,vSlot,RowGame.directed,slotEventNat_eq,h]
  | column r =>
    change directedRowNat P (vColumn r.val) (rowView p) a b=_
    simp [directedRowNat,vColumn,RowGame.directed,squaresNat_eq,dimensionNat_eq,slotNegativeNat_eq]

theorem newRuleNat_eq (P : Presentation) (q p : RowGame.Q (rows P)) (a b : ℕ) :
    newRuleNat P (rowView q) (rowView p) a b=RowGame.newRule (rows P) q p a b := by
  simp only [newRuleNat,RowGame.newRule,validRowNat_eq,directedRowNat_eq,rowView_inj]

#print axioms directedRowNat_eq
#print axioms newRuleNat_eq
end Sigma2.CompilerEffectiveCoding