import Sigma2.CompilerEventClasses

set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators
namespace Sigma2.CompilerApproxDecoder
open Compiler CompilerScaffold CompilerEventCounting

 theorem count_unique {α : Type} [DecidableEq α] (xs : List α) (a : α) (hc : xs.count a≤1) :
    ∀ (i j : ℕ) (hi : i<xs.length) (hj : j<xs.length),xs[i]=a → xs[j]=a → i=j := by
  induction xs with
  | nil => intro i j hi; simp at hi
  | cons b xs ih =>
      intro i j hi hj hi' hj'
      by_cases hb : b=a
      · subst b
        have hn : a∉xs := by
          have hz : xs.count a=0 := by simpa using hc
          exact List.count_eq_zero.mp hz
        cases i with
        | zero =>
            cases j with
            | zero => rfl
            | succ j => exact False.elim (hn (by have hx : xs[j]'(by simpa using hj)=a := hj'; rw [← hx]; exact List.getElem_mem _))
        | succ i => exact False.elim (hn (by have hx : xs[i]'(by simpa using hi)=a := hi'; rw [← hx]; exact List.getElem_mem _))
      · have hc' : xs.count a≤1 := by simpa [List.count_cons,hb,Ne.symm hb] using hc
        cases i with
        | zero => exact False.elim (hb hi')
        | succ i =>
            cases j with
            | zero => exact False.elim (hb hj')
            | succ j => exact congrArg Nat.succ (ih hc' i j (by simpa using hi) (by simpa using hj) hi' hj')

 theorem count_map_rule {α β : Type} [DecidableEq β] (xs : List α) (f : α → β) (a : β) :
    (xs.map f).count a=(xs.map (fun x => if f x=a then 1 else 0)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => by_cases hx : f x=a <;> simp [List.count_cons,hx,Ne.symm,ih,Nat.add_comm]

 theorem sum_delta_finRange (n : ℕ) (r : Fin n) :
    ((List.finRange n).map (fun i => if i=r then (1:ℕ) else 0)).sum=1 := by
  have he := count_map_rule (List.finRange n) (fun i => i) r
  simpa using he.symm

 theorem column_count {s} (R : Rows s) (r : Fin R.rowCount) :
    (RowGame.questions R).count (.column r)=1 := by
  simp [RowGame.questions,List.count_flatMap,count_map_rule,Function.comp_def,sum_delta_finRange]

 theorem reference_count {s} (R : Rows s) :
    (RowGame.questions R).count (.global true)=1 := by
  simp [RowGame.questions,List.count_flatMap,count_map_rule,Function.comp_def,sum_delta_finRange]

 theorem qa_of_decode (G : Game) (R : Rows G.scenario) (q : RowScalar.NewQ R)
    (hq : (RowGame.questions R).count q.val≤1) (hqne : q.val≠.anchor)
    (x : QA (RowGame.scenario G R)) (hx : RowGame.decodeA G R x=.inr q.val) :
    x=RowScalar.qa G R q := by
  have hnew : ¬ x.val<G.scenario.questionsA+1 := by
    intro ho
    simp only [RowGame.decodeA,dif_pos ho] at hx
    cases hx
  have hi : x.val-(G.scenario.questionsA+1)<(RowGame.questions R).length := by
    have hh := x.isLt
    dsimp [RowGame.scenario] at hh
    omega
  have hg : (RowGame.questions R)[x.val-(G.scenario.questionsA+1)]=q.val := by
    simpa only [RowGame.decodeA,dif_neg hnew,List.getElem?_eq_getElem hi,
      Option.getD_some,Sum.inr.injEq] using hx
  have hj := List.idxOf_lt_length_of_mem q.property
  have he := count_unique (RowGame.questions R) q.val hq _ _ hi hj hg
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem q.property))
  apply Fin.ext
  dsimp [RowScalar.qa]
  omega

 theorem qb_of_decode (G : Game) (R : Rows G.scenario) (q : RowScalar.NewQ R)
    (hq : (RowGame.questions R).count q.val≤1) (hqne : q.val≠.anchor)
    (x : QB (RowGame.scenario G R)) (hx : RowGame.decodeB G R x=.inr q.val) :
    x=RowScalar.qb G R q := by
  have hnew : ¬ x.val<G.scenario.questionsB+1 := by
    intro ho
    simp only [RowGame.decodeB,dif_pos ho] at hx
    cases hx
  have hi : x.val-(G.scenario.questionsB+1)<(RowGame.questions R).length := by
    have hh := x.isLt
    dsimp [RowGame.scenario] at hh
    omega
  have hg : (RowGame.questions R)[x.val-(G.scenario.questionsB+1)]=q.val := by
    simpa only [RowGame.decodeB,dif_neg hnew,List.getElem?_eq_getElem hi,
      Option.getD_some,Sum.inr.injEq] using hx
  have hj := List.idxOf_lt_length_of_mem q.property
  have he := count_unique (RowGame.questions R) q.val hq _ _ hi hj hg
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem q.property))
  apply Fin.ext
  dsimp [RowScalar.qb]
  omega

#print axioms count_unique
#print axioms column_count
#print axioms reference_count
#print axioms qa_of_decode
#print axioms qb_of_decode
end Sigma2.CompilerApproxDecoder
