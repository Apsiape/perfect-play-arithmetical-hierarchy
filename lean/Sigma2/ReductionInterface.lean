import Sigma2.Clock

noncomputable section
namespace Sigma2.Reduction
open Sigma2.Tree

abbrev RawAutomaton := ℕ × List ℕ

def automatonOfRaw (r : RawAutomaton) : Automaton where
  extraSymbols := r.1
  update := fun l c d ε =>
    if l=some 1 ∧ c=1 ∧ d=1 then 1 else
      let index := ((((l.map (fun x => x.val+1)).getD 0)*(r.1+3)+c.val)*(r.1+3)+d.val)*2+
        (if ε then 1 else 0)
      ⟨(r.2[index]?.getD 1)%(r.1+3),Nat.mod_lt _ (by omega)⟩
  blank_quiescence := by intro ε; simp

def decodeAutomaton (c : ℕ) : Automaton :=
  automatonOfRaw ((Encodable.decode (α := RawAutomaton) c).getD (0,[]))

def PrimeRank (n q : ℕ) : Prop :=
  Nat.Prime q ∧ ((Finset.range q).filter Nat.Prime).card=n

def ProgramCorrect (R : ℕ × ℕ × ℕ → Bool) (e : ℕ) (M : Automaton) : Prop :=
  (∀ q, 0<q →
    ((∀ t x, run M (fun y => decide (q ∣ y)) t x≠2) ↔
      ∃ n, PrimeRank n q ∧ ∀ t, R (e,n,t)=true)) ∧
  (∀ q, 0<q → ∀ t, t≤q → ∀ x, run M (fun y => decide (q ∣ y)) t x≠2) ∧
  (∀ pulse t x, t<x → run M pulse t x=1)

end Sigma2.Reduction
