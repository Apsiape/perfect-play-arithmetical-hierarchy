import Sigma2.SimulatorParameter
import Sigma2.SimulatorNumbered

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorParameterCoding
open Turing Sigma2.Tree Sigma2.SimulatorNumbered Sigma2.SimulatorParameter

local instance : Nonempty SimulatorLoader.Control := ⟨.origin⟩
variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]

def labelCoding (C : Coding Q) (e : ℕ) : Coding (Label e Q) where
  size := 3+2*(e+1)+C.size
  pos := by omega
  enc := fun q => match q with
    | .scan => 0
    | .sepMove => 1
    | .back => 2
    | .fill i => 3+i.val
    | .right i => 3+(e+1)+i.val
    | .run q => 3+2*(e+1)+C.enc q
  enc_lt := by
    intro q
    cases q with
    | scan => change 0<_; omega
    | sepMove => change 1<_; omega
    | back => change 2<_; omega
    | fill i => change 3+i.val<_; have := i.isLt; omega
    | right i => change 3+(e+1)+i.val<_; have := i.isLt; omega
    | run q => change 3+2*(e+1)+C.enc q<_; have := C.enc_lt q; omega
  dec := fun n => if n<3 then
      if n=0 then .scan else if n=1 then .sepMove else .back
    else if n<3+(e+1) then .fill ⟨(n-3)%(e+1), Nat.mod_lt _ (by omega)⟩
    else if n<3+2*(e+1) then .right ⟨(n-(3+(e+1)))%(e+1), Nat.mod_lt _ (by omega)⟩
    else .run (C.dec (n-(3+2*(e+1))))
  left_inv := by
    intro q
    cases q with
    | scan => simp
    | sepMove => simp
    | back => simp
    | fill i =>
      have hi := i.isLt
      have h1 : ¬3+i.val<3 := by omega
      have h2 : 3+i.val<3+(e+1) := by omega
      simp [h1, h2, Nat.mod_eq_of_lt hi]
    | right i =>
      have hi := i.isLt
      have h1 : ¬3+(e+1)+i.val<3 := by omega
      have h2 : ¬3+(e+1)+i.val<3+(e+1) := by omega
      have h3 : 3+(e+1)+i.val<3+2*(e+1) := by omega
      simp [h1, h2, h3, Nat.mod_eq_of_lt hi]
    | run q =>
      have h1 : ¬3+2*(e+1)+C.enc q<3 := by omega
      have h2 : ¬3+2*(e+1)+C.enc q<3+(e+1) := by omega
      have h3 : ¬3+2*(e+1)+C.enc q<3+2*(e+1) := by omega
      simp [h1, h2, h3]

def stateCoding (G : Coding Γ) (C : Coding Q) (e : ℕ) :
    Coding (SimulatorLoader.State Γ (Label e Q)) :=
  (Coding.fixed SimulatorLoader.Control).option.prod
    ((Coding.fixed (Fin 5)).prod
      ((G.prod (labelCoding C e).option).prod (G.prod (labelCoding C e).option)))

variable [DecidableEq Γ] [DecidableEq Q]
local instance (e : ℕ) : DecidableEq (SimulatorLoader.State Γ (Label e Q)) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

def family (M : TM0.Machine Γ Q) (a z sep : Γ) (G : Coding Γ) (C : Coding Q)
    (e : ℕ) : Automaton :=
  SimulatorNumbered.automaton (SimulatorLoader.rule (machine M a z sep e) a z)
    (stateCoding G C e)

/-- The alphabet-size formula contains only fixed constants and arithmetic in e. -/
theorem size_primrec (M : TM0.Machine Γ Q) (a z sep : Γ) (G : Coding Γ) (C : Coding Q) :
    Primrec (fun e => (family M a z sep G C e).extraSymbols) := by
  have hn : Primrec (fun e => 3+2*(e+1)+C.size+1) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp (Primrec.const 3)
          (Primrec.nat_mul.comp (Primrec.const 2) Primrec.succ)) (Primrec.const C.size))
      (Primrec.const 1)
  exact Primrec.nat_mul.comp (Primrec.const _)
    (Primrec.nat_mul.comp (Primrec.const _)
      (Primrec.nat_mul.comp
        (Primrec.nat_mul.comp (Primrec.const G.size) hn)
        (Primrec.nat_mul.comp (Primrec.const G.size) hn)))

/-- A correct family with one fixed compiled verifier, explicit finite counters,
and an explicit symbol numbering. Only local-entry computability is separate. -/
theorem correct_family (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ (Q : Type) (fQ : Fintype Q) (iQ : Inhabited Q) (dQ : DecidableEq Q)
      (M : TM0.Machine SimulatorMachine.TapeAlphabet Q),
      ∀ e, Sigma2.Reduction.ProgramCorrect R e
        (family M SimulatorStandard.unaryBody SimulatorStandard.unaryBottom
          SimulatorPair.separator (Coding.fixed SimulatorMachine.TapeAlphabet)
          (Coding.fixed Q) e) := by
  classical
  obtain ⟨Q, fQ, iQ, dQ, M, hM⟩ := program_family R hR
  letI := fQ
  letI := iQ
  letI := dQ
  refine ⟨Q, fQ, iQ, dQ, M, fun e => ?_⟩
  apply SimulatorNumbered.programCorrect
  exact hM e

#print axioms size_primrec
#print axioms correct_family
end Sigma2.SimulatorParameterCoding


