import Sigma2.UpperScenarioCoding
import Sigma2.UpperStageSemantics

namespace Sigma2.UpperGameCompiler
open Sigma2.UpperStageSyntax Sigma2.UpperRealArithmetic Sigma2.UpperEffective Primrec
open scoped BigOperators
set_option maxHeartbeats 200000

def rawWeight (r : RawGame) (x y : ℕ) : ℚ :=
  r.2.1[x * (r.1.questionsB+1) + y]?.getD 0

def rawWin (r : RawGame) (x y a b : ℕ) : Bool :=
  r.2.2[(((x * (r.1.questionsB+1) + y) * (r.1.answersA+1) + a) *
    (r.1.answersB+1) + b)]?.getD false

def rawLosing (r : RawGame) (x y a b : ℕ) : Bool :=
  decide (0 < rawWeight r x y) && !(rawWin r x y a b)

def generated (r : RawGame) (κ m : ℕ) (ε : ℚ) : Sentence :=
  amplitudeConstraints κ m ++
  normalization (r.1.questionsA+1) (r.1.answersA+1) m (evar m) ++
  normalization (r.1.questionsB+1) (r.1.answersB+1) m (fvar m) ++
  losingConstraints (r.1.questionsA+1) (r.1.questionsB+1) (r.1.answersA+1) (r.1.answersB+1)
    m (rawLosing r) ε

@[fun_prop] theorem fields_primrec : Primrec UpperScenarioCoding.fields := by
  refine (Primrec.option_getD.comp (UpperScenarioCoding.parse_primrec.comp Primrec.encode) (Primrec.const (0,0,0,0))).of_eq ?_
  intro s
  rw [← UpperScenarioCoding.code_eq_encode,UpperScenarioCoding.parse_code]
  rfl
@[fun_prop] theorem questionsA_primrec : Primrec Scenario.questionsA := Primrec.fst.comp fields_primrec
@[fun_prop] theorem questionsB_primrec : Primrec Scenario.questionsB := (Primrec.fst.comp Primrec.snd).comp fields_primrec
@[fun_prop] theorem answersA_primrec : Primrec Scenario.answersA := (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp fields_primrec
@[fun_prop] theorem answersB_primrec : Primrec Scenario.answersB := (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp fields_primrec

@[fun_prop] theorem get_primrec {α : Type*} [Primcodable α] :
    Primrec (fun p : (List α × ℕ) × α => p.1.1[p.1.2]?.getD p.2) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp (fst.comp fst) (snd.comp fst)) snd
@[fun_prop] theorem bool_and_primrec : Primrec (fun p : Bool × Bool => p.1 && p.2) :=
  Primrec.and
@[fun_prop] theorem bool_not_primrec : Primrec Bool.not := Primrec.dom_bool _
@[fun_prop] theorem rational_positive_primrec : Primrec (fun q : ℚ => decide (0 < q)) :=
  (UpperCoding.rat_lt.comp (const 0) .id).decide

@[fun_prop] theorem rawWeight_primrec : Primrec (fun p : RawGame × ℕ × ℕ => rawWeight p.1 p.2.1 p.2.2) := by
  have hi : Primrec (fun p : RawGame × ℕ × ℕ => p.2.1 * (p.1.1.questionsB+1) + p.2.2) := by fun_prop
  exact Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (fst.comp (snd.comp fst)) hi) (const 0)
@[fun_prop] theorem rawWin_primrec : Primrec (fun p : RawGame × ℕ × ℕ × ℕ × ℕ => rawWin p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hi : Primrec (fun p : RawGame × ℕ × ℕ × ℕ × ℕ =>
      (((p.2.1 * (p.1.1.questionsB+1) + p.2.2.1) * (p.1.1.answersA+1) + p.2.2.2.1) *
        (p.1.1.answersB+1) + p.2.2.2.2)) := by fun_prop
  exact Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (snd.comp (snd.comp fst)) hi) (const false)
@[fun_prop] theorem rawLosing_primrec : Primrec (fun p : RawGame × ℕ × ℕ × ℕ × ℕ => rawLosing p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  exact bool_and_primrec.comp
    ((rational_positive_primrec.comp (rawWeight_primrec.comp
      (fst.pair ((fst.comp snd).pair (fst.comp (snd.comp snd)))))).pair
      (bool_not_primrec.comp rawWin_primrec))
theorem generated_primrec : Primrec (fun p : RawGame × ℕ × ℕ × ℚ => generated p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let α := RawGame × ℕ × ℕ × ℚ
  have hqA : Primrec (fun p : α => p.1.1.questionsA+1) :=
    Primrec.succ.comp (questionsA_primrec.comp (fst.comp fst))
  have hqB : Primrec (fun p : α => p.1.1.questionsB+1) :=
    Primrec.succ.comp (questionsB_primrec.comp (fst.comp fst))
  have ha : Primrec (fun p : α => p.1.1.answersA+1) :=
    Primrec.succ.comp (answersA_primrec.comp (fst.comp fst))
  have hb : Primrec (fun p : α => p.1.1.answersB+1) :=
    Primrec.succ.comp (answersB_primrec.comp (fst.comp fst))
  have hm : Primrec (fun p : α => p.2.2.1) := fst.comp (snd.comp snd)
  have hk : Primrec (fun p : α => p.2.1) := fst.comp snd
  have hε : Primrec (fun p : α => p.2.2.2) := snd.comp (snd.comp snd)
  have hA := pr_amplitudeConstraints.comp (hk.pair hm)
  have hE := pr_normalizationE.comp (hqA.pair (ha.pair hm))
  have hF := pr_normalizationF.comp (hqB.pair (hb.pair hm))
  have hp : Primrec (fun p : α × ℕ × ℕ × ℕ × ℕ => (p.1.1,p.2)) := (fst.comp fst).pair snd
  have hL0 := rawLosing_primrec.comp hp
  have hL := pr_losingConstraints (fun p : α => p.1.1.questionsA+1)
    (fun p => p.1.1.questionsB+1) (fun p => p.1.1.answersA+1) (fun p => p.1.1.answersB+1)
    (fun p => p.2.2.1) (fun p => rawLosing p.1) (fun p => p.2.2.2)
    hqA hqB ha hb hm hL0 hε
  have hgen := list_append.comp (list_append.comp (list_append.comp hA hE) hF) hL
  exact hgen
theorem sentence_computable : Computable (fun p : RawGame × ℕ × ℕ => sentence p.1.1 p.2.1 p.2.2 (rawLosing p.1)) := by
  have he : Computable (fun p : RawGame × ℕ × ℕ => (p.2.1:ℚ)/(p.2.2+2)) := by
    refine (UpperCoding.rat_divNat.comp
      ((UpperCoding.int_ofNat.comp (fst.comp snd : Primrec (fun p : RawGame × ℕ × ℕ => p.2.1))).to_comp.pair
        (Primrec.nat_add.comp (snd.comp snd) (const 2)).to_comp)).of_eq ?_
    intro p
    simp
  have hi : Computable (fun p : RawGame × ℕ × ℕ => (p.1,p.2.1,p.2.2+1,(p.2.1:ℚ)/(p.2.2+2))) :=
    Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (((Primrec.succ.comp (snd.comp snd)).to_comp).pair he))
  have hgen := generated_primrec.to_comp.comp hi
  exact hgen

end Sigma2.UpperGameCompiler