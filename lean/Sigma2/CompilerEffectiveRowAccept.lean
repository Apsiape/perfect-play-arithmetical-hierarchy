import Sigma2.CompilerEffectiveRowDirected
noncomputable section
set_option maxHeartbeats 300000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace Sigma2.CompilerEffectiveCoding
open CompilerScaffold CompilerEffective Compiler
set_option allowUnsafeReducibility true in
attribute [local reducible] CompilerScaffold.rows CompilerScaffold.preGame CompilerScaffold.scenario RowGame.scenario
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList names rowList encodingCount
  refinementCount RowSlots.raw RowSlots.bound RowSlots.squares RowSlots.dimension
  RowSlots.slots RowSlots.slot RowGame.questions RowGame.axis RowGame.valid RowGame.directed
  CompilerScaffold.question CompilerScaffold.rule RowGame.parity RowGame.scalarClass RowGame.bitAnswer
  validRowNat directedRowNat newRuleNat bindOldANat bindOldBNat oldSyncNat
  questionLookupNat decodeRowNat acceptsRowNat questionsNat slotNat

theorem questionLookupNat_eq (P : Presentation) (x : ℕ) :
    questionLookupNat P x=rowView ((RowGame.questions (rows P))[x-((scenario P).questionsA+1)]?.getD .anchor) := by
  unfold questionLookupNat
  exact questionLookup_eq P _

theorem acceptsRowNat_eq (P : Presentation)
    (x : QA (RowGame.scenario (preGame P) (rows P)))
    (y : QB (RowGame.scenario (preGame P) (rows P)))
    (a : AA (RowGame.scenario (preGame P) (rows P)))
    (b : BB (RowGame.scenario (preGame P) (rows P))) :
    acceptsRowNat P x.val y.val a.val b.val=RowGame.accepts (preGame P) (rows P) x y a b := by
  have hd (u : QA (scenario P)) (v : QB (scenario P)) : (preGame P).distribution u v≠0 :=
    ne_of_gt (pre_distribution_positive P u v)
  unfold acceptsRowNat RowGame.accepts RowGame.decodeA RowGame.decodeB
  by_cases hx : x.val<(scenario P).questionsA+1 <;> by_cases hy : y.val<(scenario P).questionsA+1
  · simp only [ite_eq_left hx,dite_eq_left hx,ite_eq_left hy,dite_eq_left hy]
    by_cases ha : a.val<12 <;> by_cases hb : b.val<12
    · let ox : QA (scenario P) := ⟨x.val,hx⟩
      let oy : QB (scenario P) := ⟨y.val,hy⟩
      let oa : AA (scenario P) := ⟨a.val,ha⟩
      let ob : BB (scenario P) := ⟨b.val,hb⟩
      have hp := preAcceptsNat_eq P ox oy oa ob
      have hs := oldSyncNat_eq P ox oy a.val b.val
      simp only [ite_eq_left ha,dite_eq_left ha,ite_eq_left hb,dite_eq_left hb]
      rw [ite_eq_right (hd ox oy)]
      exact congrArg₂ Bool.and hp hs
    · simp [ha,hb]
    · simp [ha,hb]
    · simp [ha,hb]
  · simp only [ite_eq_left hx,dite_eq_left hx,ite_eq_right hy,dite_eq_right hy]
    let ox : QA (scenario P) := ⟨x.val,hx⟩
    let op : RowGame.Q (rows P) := (RowGame.questions (rows P))[y.val-((scenario P).questionsA+1)]?.getD .anchor
    have hv := questionLookupNat_eq P y.val
    have hvalid := validRowNat_eq P op b.val
    have hbind := bindOldANat_eq P ox op a.val b.val
    have hvalid' := (congrArg (fun p => validRowNat P p b.val) hv).trans hvalid
    have hbind' := (congrArg (fun p => bindOldANat P ox.val p a.val b.val) hv).trans hbind
    exact congrArg₂ Bool.and (congrArg (fun v => decide (a.val<12) && v) hvalid') hbind'
  · simp only [ite_eq_right hx,dite_eq_right hx,ite_eq_left hy,dite_eq_left hy]
    let oy : QB (scenario P) := ⟨y.val,hy⟩
    let oq : RowGame.Q (rows P) := (RowGame.questions (rows P))[x.val-((scenario P).questionsA+1)]?.getD .anchor
    have hv := questionLookupNat_eq P x.val
    have hvalid := validRowNat_eq P oq a.val
    have hbind := bindOldBNat_eq P oq oy a.val b.val
    have hvalid' := (congrArg (fun q => validRowNat P q a.val) hv).trans hvalid
    have hbind' := (congrArg (fun q => bindOldBNat P q oy.val a.val b.val) hv).trans hbind
    exact congrArg₂ Bool.and (congrArg (fun v => v && decide (b.val<12)) hvalid') hbind'
  · simp only [ite_eq_right hx,dite_eq_right hx,ite_eq_right hy,dite_eq_right hy]
    exact (congrArg₂ (fun q p => newRuleNat P q p a.val b.val)
      (questionLookupNat_eq P x.val) (questionLookupNat_eq P y.val)).trans
      (newRuleNat_eq P _ _ a.val b.val)

theorem final_acceptsNat_eq (P : Presentation) (x : QA (finalGame P).scenario) (y : QB (finalGame P).scenario)
    (a : AA (finalGame P).scenario) (b : BB (finalGame P).scenario) :
    acceptsRowNat P x.val y.val a.val b.val=(finalGame P).accepts x y a b := acceptsRowNat_eq P x y a b

#print axioms acceptsRowNat_eq
#print axioms final_acceptsNat_eq
end Sigma2.CompilerEffectiveCoding