import Sigma2.Statements
import Mathlib.Computability.TuringMachine.ToPartrec

noncomputable section
set_option synthInstance.maxHeartbeats 10000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000
open Turing
namespace Sigma2.SimulatorMachine
open PartrecToTM2

/-- The concrete natural-number result convention used by the Mathlib compiler. -/
def result (R : ℕ × ℕ × ℕ → Bool) (v : List.Vector ℕ 3) : ℕ :=
  Encodable.encode (R (v.head, v.tail.head, v.tail.tail.head))

theorem result_computable (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    Computable (result R) := by
  exact Computable.encode.comp (hR.comp
    (Computable.vector_head.pair ((Computable.vector_head.comp Computable.vector_tail).pair
      (Computable.vector_head.comp (Computable.vector_tail.comp Computable.vector_tail)))))

/-- Extract an actual partial-recursive program, with exact total semantics. -/
theorem exists_code (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ c : ToPartrec.Code, ∀ v : List.Vector ℕ 3,
      c.eval v.val = Part.some [result R v] := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.of_part (result_computable R hR).partrec)
  refine ⟨c, fun v => ?_⟩
  simpa only [PFun.coe_val, Part.map_eq_map, Part.map_some, List.pure_def] using hc v

abbrev TapeAlphabet := TM2to1.Γ' K' (fun _ : K' => Γ')
abbrev Labels1 := TM2to1.Λ' K' (fun _ : K' => Γ') Λ' (Option Γ')

def machine1 : Labels1 → TM1.Stmt TapeAlphabet Labels1 (Option Γ') := TM2to1.tr tr
abbrev Labels0 := TM1to0.Λ' machine1

def input (v : List ℕ) : List TapeAlphabet := TM2to1.trInit K'.main (trList v)

def runCode (c : ToPartrec.Code) (v : List ℕ) : Part (ListBlank TapeAlphabet) :=
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  TM0.eval (TM1to0.tr machine1) (input v)

/-- The initial state of the stack-machine compiler agrees with the standard
TM2 input configuration when the code entry label is selected. -/
theorem init_eq (c : ToPartrec.Code) (v : List ℕ) :
    letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
    TM2.init K'.main (trList v) = PartrecToTM2.init c v := by
  unfold TM2.init PartrecToTM2.init
  congr 1
  funext k
  cases k <;> simp [K'.elim]

/-- Mathlib's program-to-TM2 correctness theorem, in its stack-output interface. -/
theorem tm2_eval (c : ToPartrec.Code) (v : List ℕ) :
    letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
    TM2.eval tr K'.main (trList v) = trList <$> c.eval v := by
  unfold TM2.eval
  rw [init_eq, PartrecToTM2.tr_eval]
  rfl

/-- The compiled TM0 and TM1 have exactly the same output tape semantics. -/
theorem tm0_eval (c : ToPartrec.Code) (v : List ℕ) :
    letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
    runCode c v = TM1.eval machine1 (input v) := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  exact TM1to0.tr_eval machine1 (input v)

/-- Mathlib's TM2-to-TM1 and TM1-to-TM0 translations preserve halting. -/
theorem runCode_dom (c : ToPartrec.Code) (v : List ℕ) :
    (runCode c v).Dom ↔ (c.eval v).Dom := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  rw [tm0_eval]
  change (TM1.eval (TM2to1.tr tr) (TM2to1.trInit K'.main (trList v))).Dom ↔ _
  rw [TM2to1.tr_eval_dom, tm2_eval]
  rfl

/-- The four-stack source has a finite stack-index type and finite tape alphabet. -/
instance stackFintype : Fintype K' where
  elems := {K'.main, K'.rev, K'.aux, K'.stack}
  complete := by intro k; cases k <;> simp

instance alphabetFintype : Fintype TapeAlphabet := inferInstance

/-- The full compilation chain retains a finite set of reachable machine states. -/
theorem finite_support (c : ToPartrec.Code) :
    letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
    ∃ S : Finset Labels0, TM0.Supports (TM1to0.tr machine1) (S : Set Labels0) := by
  classical
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have hs2 := PartrecToTM2.tr_supports c Cont'.halt
  have hs1 := TM2to1.tr_supports tr hs2
  exact ⟨_, TM1to0.tr_supports machine1 hs1⟩

/-- The projected main stack is the exact encoded output, with Mathlib's
stack-order convention (the tape stores each stack in reverse). -/
def OutputEncodes (w : ListBlank TapeAlphabet) (out : List ℕ) : Prop :=
  (w.map ⟨Prod.snd, rfl⟩).map (proj K'.main) =
    ListBlank.mk ((trList out).map some).reverse

/-- Exact output correctness through both machine translations. -/
theorem runCode_output (c : ToPartrec.Code) (v out : List ℕ)
    (hc : c.eval v = Part.some out) :
    ∃ w ∈ runCode c v, OutputEncodes w out := by
  letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
  have h2 : TM2.eval tr K'.main (trList v) = Part.some (trList out) := by
    rw [tm2_eval, hc]
    rfl
  have hdom : (runCode c v).Dom := (runCode_dom c v).mpr (by rw [hc]; trivial)
  obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp hdom
  have h1 : w ∈ TM1.eval (TM2to1.tr tr) (TM2to1.trInit K'.main (trList v)) := by
    change w ∈ TM1.eval machine1 (input v)
    rw [← tm0_eval c v]
    exact hw
  have h2mem : trList out ∈ TM2.eval tr K'.main (trList v) := by rw [h2]; simp
  obtain ⟨S, L, hL, hproj, hmain⟩ := TM2to1.tr_eval tr K'.main (trList v) h1 h2mem
  refine ⟨w, hw, ?_⟩
  unfold OutputEncodes
  rw [← hL, TM2to1.addBottom_map, hproj, hmain]

/-- A computable predicate yields a finite-supported TM0 with exact encoded
Boolean output on every three-number input. This is the machine-extraction part
of the effective-program construction; it does not assert a CA simulation. -/
theorem computable_predicate_machine (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ c : ToPartrec.Code, ∀ v : List.Vector ℕ 3,
      ∃ w ∈ runCode c v.val, OutputEncodes w [result R v] := by
  obtain ⟨c, hc⟩ := exists_code R hR
  exact ⟨c, fun v => runCode_output c v.val [result R v] (hc v)⟩

#print axioms finite_support
#print axioms runCode_output
#print axioms computable_predicate_machine
#print axioms exists_code
#print axioms tm2_eval
#print axioms tm0_eval
#print axioms runCode_dom
end Sigma2.SimulatorMachine
