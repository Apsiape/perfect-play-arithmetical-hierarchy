import Sigma2.CompilerEffectiveRowView
noncomputable section
set_option maxHeartbeats 250000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective Compiler
set_option allowUnsafeReducibility true in
attribute [local reducible] CompilerScaffold.rows
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList encodingCount refinementCount scenario RowSlots.raw RowSlots.bound RowSlots.squares RowSlots.dimension RowSlots.slots RowSlots.slot RowGame.questions RowGame.axis
  RowGame.parity RowGame.scalarClass RowGame.bitAnswer questionsNat slotNat dimensionNat squaresNat
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.cond
  Computable.sumInl Computable.sumInr
variable {α : Type} [Primcodable α]

@[fun_prop] theorem cparity (bits mask value : α → ℕ)
    (hbits : Computable bits) (hmask : Computable mask) (hvalue : Computable value) :
    Computable (fun a => RowGame.parity (bits a) (mask a) (value a)) := by
  unfold RowGame.parity
  exact cfoldl (fun a => List.range (bits a)) (fun _ => false)
    (fun a z => Bool.xor z.1 (Nat.testBit (mask a) z.2 && Nat.testBit (value a) z.2))
    (crange _ hbits) (Computable.const false) (by fun_prop)
@[fun_prop] theorem cscalarClass (a : α → ℕ) (ha : Computable a) :
    Computable (fun z => RowGame.scalarClass (a z)) := by unfold RowGame.scalarClass; fun_prop
@[fun_prop] theorem cbitAnswer (a : α → Bool) (ha : Computable a) :
    Computable (fun z => RowGame.bitAnswer (a z)) := by unfold RowGame.bitAnswer; fun_prop

def validRowNat (P : Presentation) (q : RowQuestionData) (a : ℕ) : Bool :=
  if q.1=0 then decide (a=1)
  else if q.1=1 then decide (a<2)
  else if q.1=2 then decide (a<4)
  else if q.1=3 then if q.2.1=q.2.2.1 then decide (a=0) else decide (a<4)
  else if q.1=4 then decide (a<4)
  else if q.1=5 then decide (a<dimensionNat P)
  else if q.1=6 then decide (a<2*dimensionNat P ∧ a/2≤Nat.xor (a/2) q.2.1)
  else if q.1=7 then decide (a<6)
  else if q.1=8 then decide (a<dimensionNat P)
  else true

def directedRowNat (P : Presentation) (q p : RowQuestionData) (a b : ℕ) : Bool :=
  if q.1=2 then
    (List.range 3).all (fun j =>
      let cell := if q.2.2.2.2.2 then vCell q.2.1 j q.2.2.1 else vCell q.2.1 q.2.2.1 j
      if p=cell then decide (b=RowGame.bitAnswer (cellSign (q.2.2.2.2.2 && decide (q.2.2.1=2)) a j)) else true)
  else if q.1=3 then
    if q.2.1=q.2.2.1 then true else
      (if p=axisView q.2.1 q.2.2.2.1 then decide (b=a/2) else true) &&
      (if p=axisView q.2.2.1 q.2.2.2.2.1 then decide (b=a%2) else true)
  else if q.1=4 then
    if p=axisView q.2.2.1 q.2.2.2.1 then decide (b=a%2) else true
  else if q.1=5 then
    (List.range (squaresNat P)).all (fun g => (List.range 2).all (fun k =>
      let ax := k+if q.2.2.2.2.2 then 2 else 0
      if p=axisView g ax then decide (b=RowGame.bitAnswer (Nat.testBit a (2*g+k))) else true))
  else if q.1=6 then
    (if p=vGlobal true then decide (decide (a%2=1)=RowGame.parity (2*squaresNat P) q.2.1 b) else true) &&
    (if p=vGlobal false then (List.range (dimensionNat P)).all (fun ell =>
      if RowGame.parity (2*squaresNat P) ell q.2.1 then true else
        decide (RowGame.parity (2*squaresNat P) ell (a/2)=RowGame.parity (2*squaresNat P) ell b)) else true)
  else if q.1=7 then
    (if p=vPair q.2.2.1 then decide (a%3=RowGame.scalarClass b) else true) &&
    (if (slotNat P q.2.1 q.2.2.1).1=none then
      if p=vAnchor then decide (a/3=b) else true else true)
  else if q.1=8 then
    (if p=vGlobal true then !(decide (a=0) && decide (b=0)) else true) &&
    ((List.range (dimensionNat P)).drop 1).all (fun j =>
      if p=vSlot q.2.1 j then if b%3=2 then true else
        let vneg := Bool.xor (decide (b/3=0)) (slotNat P q.2.1 j).2
        decide (Bool.xor (decide (b%3=1)) vneg=RowGame.parity (2*squaresNat P) a j)
      else true)
  else true

def newRuleNat (P : Presentation) (q p : RowQuestionData) (a b : ℕ) : Bool :=
  validRowNat P q a && validRowNat P p b && (if q=p then decide (a=b) else true) &&
    directedRowNat P q p a b && directedRowNat P p q b a

def bindOldANat (P : Presentation) (x : ℕ) (q : RowQuestionData) (a b : ℕ) : Bool :=
  if q.1=4 then if x=q.2.1 then decide ((a=1) ↔ b/2=1) else true
  else if q.1=7 then
    let ev := (slotNat P q.2.1 q.2.2.1).1
    if ev=none then decide (b/3=1)
    else if x=ev.getD 0 then decide ((a=1) ↔ b/3=1) else true
  else true

def bindOldBNat (P : Presentation) (q : RowQuestionData) (y : ℕ) (a b : ℕ) : Bool :=
  if q.1=4 then if y=q.2.1 then decide ((b=1) ↔ a/2=1) else true
  else if q.1=7 then
    let ev := (slotNat P q.2.1 q.2.2.1).1
    if ev=none then decide (a/3=1)
    else if y=ev.getD 0 then decide ((b=1) ↔ a/3=1) else true
  else true

def oldSyncNat (P : Presentation) (x y a b : ℕ) : Bool :=
  (List.range (names P).length).all (fun i =>
    if x=i ∧ y=i then decide (a=1 ↔ b=1) else true)

def questionLookupNat (P : Presentation) (x : ℕ) : RowQuestionData :=
  (questionsNat P)[x-((scenario P).questionsA+1)]?.getD vAnchor

def decodeRowNat (P : Presentation) (x : ℕ) : ℕ ⊕ RowQuestionData :=
  if x<(scenario P).questionsA+1 then .inl x else .inr (questionLookupNat P x)

def acceptsRowNat (P : Presentation) (x y a b : ℕ) : Bool :=
  if x<(scenario P).questionsA+1 then
    if y<(scenario P).questionsA+1 then
      if a<12 then if b<12 then preAcceptsNat P x y a b && oldSyncNat P x y a b else false else false
    else decide (a<12) && validRowNat P (questionLookupNat P y) b &&
      bindOldANat P x (questionLookupNat P y) a b
  else if y<(scenario P).questionsA+1 then
    validRowNat P (questionLookupNat P x) a && decide (b<12) &&
      bindOldBNat P (questionLookupNat P x) y a b
  else newRuleNat P (questionLookupNat P x) (questionLookupNat P y) a b
attribute [local irreducible] validRowNat directedRowNat newRuleNat bindOldANat bindOldBNat
  oldSyncNat questionLookupNat decodeRowNat acceptsRowNat

@[fun_prop] theorem cvalidRowNat (P : α → Presentation) (q : α → RowQuestionData) (a : α → ℕ)
    (hP : Computable P) (hq : Computable q) (ha : Computable a) :
    Computable (fun z => validRowNat (P z) (q z) (a z)) := by
  unfold validRowNat
  simp only [← Bool.cond_decide,bool_decide_and,bool_decide_or,bool_decide_iff]
  fun_prop

@[fun_prop] theorem cdirectedRowNat (P : α → Presentation) (q p : α → RowQuestionData) (a b : α → ℕ)
    (hP : Computable P) (hq : Computable q) (hp : Computable p) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => directedRowNat (P z) (q z) (p z) (a z) (b z)) := by
  unfold directedRowNat
  simp only [← Bool.cond_decide,bool_decide_and,bool_decide_or,bool_decide_iff]
  fun_prop

@[fun_prop] theorem cnewRuleNat (P : α → Presentation) (q p : α → RowQuestionData) (a b : α → ℕ)
    (hP : Computable P) (hq : Computable q) (hp : Computable p) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => newRuleNat (P z) (q z) (p z) (a z) (b z)) := by unfold newRuleNat; fun_prop

@[fun_prop] theorem cbindOldANat (P : α → Presentation) (x : α → ℕ) (q : α → RowQuestionData) (a b : α → ℕ)
    (hP : Computable P) (hx : Computable x) (hq : Computable q) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => bindOldANat (P z) (x z) (q z) (a z) (b z)) := by
  unfold bindOldANat
  simp only [← Bool.cond_decide,bool_decide_and,bool_decide_or,bool_decide_iff]
  fun_prop
@[fun_prop] theorem cbindOldBNat (P : α → Presentation) (q : α → RowQuestionData) (y : α → ℕ) (a b : α → ℕ)
    (hP : Computable P) (hq : Computable q) (hy : Computable y) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => bindOldBNat (P z) (q z) (y z) (a z) (b z)) := by
  unfold bindOldBNat
  simp only [← Bool.cond_decide,bool_decide_and,bool_decide_or,bool_decide_iff]
  fun_prop
@[fun_prop] theorem coldSyncNat (P : α → Presentation) (x y a b : α → ℕ)
    (hP : Computable P) (hx : Computable x) (hy : Computable y) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => oldSyncNat (P z) (x z) (y z) (a z) (b z)) := by
  unfold oldSyncNat
  simp only [← Bool.cond_decide,bool_decide_and,bool_decide_or,bool_decide_iff]
  fun_prop
@[fun_prop] theorem cquestionLookupNat (P : α → Presentation) (x : α → ℕ) (hP : Computable P) (hx : Computable x) :
    Computable (fun z => questionLookupNat (P z) (x z)) := by
  have hc := pre_count_computable.comp hP
  unfold questionLookupNat
  fun_prop
@[fun_prop] theorem cdecodeRowNat (P : α → Presentation) (x : α → ℕ) (hP : Computable P) (hx : Computable x) :
    Computable (fun z => decodeRowNat (P z) (x z)) := by
  have hc := pre_count_computable.comp hP
  unfold decodeRowNat
  fun_prop
@[fun_prop] theorem cpreAcceptsNat (P : α → Presentation) (x y a b : α → ℕ)
    (hP : Computable P) (hx : Computable x) (hy : Computable y) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => preAcceptsNat (P z) (x z) (y z) (a z) (b z)) :=
  preAcceptsNat_computable.comp (hP.pair (hx.pair (hy.pair (ha.pair hb))))
@[fun_prop] theorem cacceptsRowNat (P : α → Presentation) (x y a b : α → ℕ)
    (hP : Computable P) (hx : Computable x) (hy : Computable y) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => acceptsRowNat (P z) (x z) (y z) (a z) (b z)) := by
  have hc := pre_count_computable.comp hP
  unfold acceptsRowNat
  fun_prop

#print axioms cparity
#print axioms cvalidRowNat
#print axioms cdirectedRowNat
#print axioms cnewRuleNat
#print axioms cbindOldANat
#print axioms coldSyncNat
#print axioms cdecodeRowNat
#print axioms cacceptsRowNat
end Sigma2.CompilerEffectiveCoding