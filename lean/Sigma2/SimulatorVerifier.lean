import Sigma2.SimulatorChecks
import Sigma2.SimulatorFinite

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
namespace Sigma2.SimulatorVerifier
open Turing Sigma2.SimulatorChecks Sigma2.Reduction

/-- Unbounded sequential search for a failing verification stage. -/
def rejectSearch (R : ℕ × ℕ × ℕ → Bool) (v : List.Vector ℕ 2) : Part ℕ :=
  Nat.rfind (fun t => Part.some (!(verifyStage R v.head v.tail.head t)))

theorem rejectSearch_partrec (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    Partrec (rejectSearch R) := by
  have hs : Computable (fun x : List.Vector ℕ 2 × ℕ =>
      verifyStage R x.1.head x.1.tail.head x.2) :=
    (verifyStage_computable R hR).comp
      ((Computable.vector_head.comp Computable.fst).pair
        ((Computable.vector_head.comp (Computable.vector_tail.comp Computable.fst)).pair
          Computable.snd))
  have hb : Computable (fun x : List.Vector ℕ 2 × ℕ =>
      !(verifyStage R x.1.head x.1.tail.head x.2)) := Primrec.not.to_comp.comp hs
  exact Partrec.rfind hb.partrec.to₂

/-- The search halts exactly for a nonprime period or an eventual failed check. -/
theorem rejectSearch_dom (R : ℕ × ℕ × ℕ → Bool) (v : List.Vector ℕ 2) :
    (rejectSearch R v).Dom ↔
      ¬ ∃ n, PrimeRank n v.tail.head ∧ ∀ t, R (v.head,n,t)=true := by
  rw [← verifyStage_all]
  constructor
  · intro h hall
    obtain ⟨t, ht, _⟩ := Nat.rfind_dom.mp h
    simpa [hall t] using ht
  · intro h
    obtain ⟨t, ht⟩ := not_forall.mp h
    apply Nat.rfind_dom.mpr
    refine ⟨t, ?_, fun {_} _ => trivial⟩
    cases hv : verifyStage R v.head v.tail.head t <;> simp_all

/-- A finite failed stage is always reached, and every earlier stage passes. -/
theorem rejectSearch_first (R : ℕ × ℕ × ℕ → Bool) (v : List.Vector ℕ 2) (t : ℕ)
    (ht : t ∈ rejectSearch R v) :
    verifyStage R v.head v.tail.head t=false ∧
      ∀ s<t, verifyStage R v.head v.tail.head s=true := by
  obtain ⟨h, hmin⟩ := Nat.mem_rfind.mp ht
  constructor
  · simpa using h
  · intro s hs
    simpa using hmin hs

/-- Extract an actual list program for the partial sequential rejection search. -/
theorem exists_code (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ c : ToPartrec.Code, ∀ v : List.Vector ℕ 2,
      c.eval v.val = (fun t => [t]) <$> rejectSearch R v := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code
    (Nat.Partrec'.of_part (rejectSearch_partrec R hR))
  exact ⟨c, fun v => (hc v).trans (by rfl)⟩

/-- The extracted TM0 halts exactly on rejection; successful predicates keep
checking forever. There is no fixed time bound on an individual computation. -/
theorem code_halting (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ c : ToPartrec.Code, ∀ v : List.Vector ℕ 2,
      (SimulatorMachine.runCode c v.val).Dom ↔
        ¬ ∃ n, PrimeRank n v.tail.head ∧ ∀ t, R (v.head,n,t)=true := by
  obtain ⟨c, hc⟩ := exists_code R hR
  refine ⟨c, fun v => ?_⟩
  rw [SimulatorMachine.runCode_dom, hc]
  exact rejectSearch_dom R v

/-- The sequential verifier can itself be restricted to a genuinely finite
state type, retaining exact halting versus nonhalting behavior. -/
theorem finite_verifier (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Inhabited Q)
      (M : TM0.Machine SimulatorMachine.TapeAlphabet Q),
      ∀ v : List.Vector ℕ 2,
        (TM0.eval M (SimulatorMachine.input v.val)).Dom ↔
          ¬ ∃ n, PrimeRank n v.tail.head ∧ ∀ t, R (v.head,n,t)=true := by
  classical
  obtain ⟨c, hc⟩ := code_halting R hR
  letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  obtain ⟨S, hs⟩ := SimulatorMachine.finite_support c
  let M := TM1to0.tr SimulatorMachine.machine1
  letI : Fact ((default : SimulatorMachine.Labels0) ∈ S) := ⟨hs.1⟩
  refine ⟨{q // q ∈ S}, inferInstance, inferInstance, SimulatorFinite.machine M S hs, ?_⟩
  intro v
  rw [SimulatorFinite.eval_exact M S hs]
  exact hc v

#print axioms rejectSearch_partrec
#print axioms rejectSearch_dom
#print axioms rejectSearch_first
#print axioms exists_code
#print axioms code_halting
#print axioms finite_verifier
end Sigma2.SimulatorVerifier

