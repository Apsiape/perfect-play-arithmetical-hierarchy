import Sigma2.SimulatorStandard

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace Sigma2.SimulatorPair
open Turing Sigma2.Reduction

/-- Decode both unary blocks with one fixed list program. -/
theorem decoder_code :
    ∃ d : ToPartrec.Code, ∀ e q,
      d.eval [SimulatorUnary.ones e, SimulatorUnary.ones q] = Part.some [e,q] := by
  obtain ⟨d, hd⟩ := SimulatorUnary.decoder_code
  refine ⟨.cons (.comp d .head) (.comp d .tail), fun e q => ?_⟩
  simp [hd]

/-- One code, independent of both numbers, checks the exact rejection predicate. -/
theorem verifier_code (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ c : ToPartrec.Code, ∀ e q,
      (c.eval [SimulatorUnary.ones e, SimulatorUnary.ones q]).Dom ↔
        ¬ ∃ n, PrimeRank n q ∧ ∀ t, R (e,n,t)=true := by
  obtain ⟨c, hc⟩ := SimulatorVerifier.exists_code R hR
  obtain ⟨d, hd⟩ := decoder_code
  refine ⟨.comp c d, fun e q => ?_⟩
  have he := hc (⟨[e,q], rfl⟩ : List.Vector ℕ 2)
  have hcomp : (ToPartrec.Code.comp c d).eval [SimulatorUnary.ones e, SimulatorUnary.ones q] =
      c.eval [e,q] := by
    change (d.eval _).bind (fun w => c.eval w) = _
    rw [hd]
    exact Part.bind_some _ _
  rw [hcomp, he]
  exact SimulatorVerifier.rejectSearch_dom R _

/-- Compile once and choose the finite support once, before e is introduced. -/
theorem finite_verifier (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Inhabited Q)
      (M : TM0.Machine SimulatorMachine.TapeAlphabet Q), ∀ e q,
        (TM0.eval M (SimulatorMachine.input
          [SimulatorUnary.ones e, SimulatorUnary.ones q])).Dom ↔
          ¬ ∃ n, PrimeRank n q ∧ ∀ t, R (e,n,t)=true := by
  classical
  obtain ⟨c, hc⟩ := verifier_code R hR
  letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  obtain ⟨S, hs⟩ := SimulatorMachine.finite_support c
  let M := TM1to0.tr SimulatorMachine.machine1
  letI : Fact ((default : SimulatorMachine.Labels0) ∈ S) := ⟨hs.1⟩
  refine ⟨{q // q ∈ S}, inferInstance, inferInstance, SimulatorFinite.machine M S hs, ?_⟩
  intro e q
  rw [SimulatorFinite.eval_exact M S hs]
  change (SimulatorMachine.runCode c [SimulatorUnary.ones e, SimulatorUnary.ones q]).Dom ↔ _
  rw [SimulatorMachine.runCode_dom]
  exact hc e q

open PartrecToTM2 in
/-- The non-bottom list separator between the two captured blocks. -/
def separator : SimulatorMachine.TapeAlphabet :=
  (false, Function.update (fun _ => none) K'.main (some Γ'.cons))

/-- The exact two-number input layout, in physical tape order. -/
theorem input_pair (e q : ℕ) :
    SimulatorMachine.input [SimulatorUnary.ones e, SimulatorUnary.ones q] =
      SimulatorStandard.unaryBottom ::
        (List.replicate q SimulatorStandard.unaryBody ++
          separator :: List.replicate e SimulatorStandard.unaryBody) := by
  simp [SimulatorMachine.input, PartrecToTM2.trList, SimulatorUnary.trNat_ones,
    TM2to1.trInit, SimulatorStandard.unaryBottom, SimulatorStandard.unaryBody,
    separator, List.reverse_append, List.map_append, List.append_assoc]

#print axioms decoder_code
#print axioms verifier_code
#print axioms finite_verifier
#print axioms input_pair
end Sigma2.SimulatorPair

