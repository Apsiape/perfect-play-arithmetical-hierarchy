import Sigma2.SimulatorUniform

noncomputable section
set_option maxHeartbeats 800000
namespace Sigma2.SimulatorFixedTable
open Sigma2.Tree

/-- A fixed, arbitrarily chosen finite transition table is primitive recursive.
Only its numeric coordinate decoder varies; no effective choice is asserted. -/
theorem localEntry_primrec (M : Automaton) : Primrec (SimulatorEncoding.localEntry M) := by
  let n := M.extraSymbols+3
  have hn : 0<n := by dsimp [n]; omega
  have hdiv : Primrec (fun k : ℕ => k/2) := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hdivn : Primrec (fun k : ℕ => k/2/n) := Primrec.nat_div.comp hdiv (Primrec.const n)
  have ha : Primrec (fun k : ℕ => k/2/n/n) := Primrec.nat_div.comp hdivn (Primrec.const n)
  have hc : Primrec (fun k : ℕ => (⟨(k/2/n)%n, Nat.mod_lt _ hn⟩ : Fin n)) :=
    Primrec.fin_val_iff.mp (Primrec.nat_mod.comp hdivn (Primrec.const n))
  have hr : Primrec (fun k : ℕ => (⟨(k/2)%n, Nat.mod_lt _ hn⟩ : Fin n)) :=
    Primrec.fin_val_iff.mp (Primrec.nat_mod.comp hdiv (Primrec.const n))
  have hlv : Primrec (fun k : ℕ => (⟨(k/2/n/n-1)%n, Nat.mod_lt _ hn⟩ : Fin n)) :=
    Primrec.fin_val_iff.mp (Primrec.nat_mod.comp
      (Primrec.nat_sub.comp ha (Primrec.const 1)) (Primrec.const n))
  have hl : Primrec (fun k : ℕ => if k/2/n/n=0 then none else
      some (⟨(k/2/n/n-1)%n, Nat.mod_lt _ hn⟩ : Fin n)) :=
    Primrec.ite (Primrec.eq.comp ha (Primrec.const 0)) (Primrec.const none)
      (Primrec.option_some.comp hlv)
  have hb : Primrec (fun k : ℕ => decide (k%2=1)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 1)).decide
  have ht := Primrec.dom_finite (fun v : Option (Fin n) × Fin n × Fin n × Bool =>
    (M.update v.1 v.2.1 v.2.2.1 v.2.2.2).val)
  exact ht.comp (hl.pair (hc.pair (hr.pair hb)))

#print axioms localEntry_primrec
end Sigma2.SimulatorFixedTable
