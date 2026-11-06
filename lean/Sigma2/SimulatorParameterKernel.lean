import Sigma2.SimulatorParameterCoding
import Sigma2.SimulatorPrimrec

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
namespace Sigma2.SimulatorParameterKernel
open Turing Sigma2.SimulatorNumbered Sigma2.SimulatorParameter Sigma2.SimulatorParameterCoding

variable {Γ Q : Type} [Inhabited Γ] [Inhabited Q]

def stmtEquiv : TM0.Stmt Γ ≃ Bool ⊕ Γ where
  toFun := fun s => match s with
    | .move .left => .inl false | .move .right => .inl true | .write a => .inr a
  invFun := fun s => match s with
    | .inl false => .move .left | .inl true => .move .right | .inr a => .write a
  left_inv := by intro s; cases s with | move d => cases d <;> rfl | write a => rfl
  right_inv := by intro s; cases s with | inl b => cases b <;> rfl | inr a => rfl

instance [Primcodable Γ] : Primcodable (TM0.Stmt Γ) :=
  Primcodable.ofEquiv (Bool ⊕ Γ) stmtEquiv
instance [Fintype Γ] : Fintype (TM0.Stmt Γ) :=
  Fintype.ofEquiv (Bool ⊕ Γ) stmtEquiv.symm

variable [Fintype Γ] [Fintype Q] [Primcodable Γ] [Primcodable Q]
  [DecidableEq Γ] [DecidableEq Q]

@[fun_prop] theorem write_primrec : Primrec (@TM0.Stmt.write Γ) := Primrec.dom_finite _
def normalize (e k : ℕ) : ℕ :=
  (labelCoding (Coding.fixed Q) e).enc ((labelCoding (Coding.fixed Q) e).dec k)

def normalizeNumeric (e k : ℕ) : ℕ :=
  if k<3 then if k=0 then 0 else if k=1 then 1 else 2
  else if k<3+(e+1) then 3+(k-3)%(e+1)
  else if k<3+2*(e+1) then 3+(e+1)+(k-(3+(e+1)))%(e+1)
  else 3+2*(e+1)+(Coding.fixed Q).enc ((Coding.fixed Q).dec (k-(3+2*(e+1))))

lemma normalize_eq (e k : ℕ) : normalize (Q:=Q) e k=normalizeNumeric (Q:=Q) e k := by
  unfold normalize normalizeNumeric labelCoding
  dsimp only
  split_ifs <;> simp_all

/-- Even redundant numeric labels have a computable canonicalization. -/
theorem normalize_primrec : Primrec₂ (normalize (Q:=Q)) := by
  have h : Primrec (fun p : ℕ × ℕ => normalizeNumeric (Q:=Q) p.1 p.2) := by
    unfold normalizeNumeric
    fun_prop
  exact h.of_eq fun p => (normalize_eq p.1 p.2).symm
def transition (M : TM0.Machine Γ Q) (a z sep : Γ) (e : ℕ) (v : ℕ × Γ) :
    Option (ℕ × TM0.Stmt Γ) :=
  (machine M a z sep e ((labelCoding (Coding.fixed Q) e).dec v.1) v.2).map
    (fun p => ((labelCoding (Coding.fixed Q) e).enc p.1,p.2))

def transitionNumeric (M : TM0.Machine Γ Q) (a z sep : Γ) (e : ℕ) (v : ℕ × Γ) :
    Option (ℕ × TM0.Stmt Γ) :=
  let k := v.1
  let s := v.2
  if k<3 then
    if k=0 then
      if s=default then some (1,.write sep) else some (0,.move .right)
    else if k=1 then some (3+e,.move .right)
    else if s=z then some (3+2*(e+1)+(Coding.fixed Q).enc default,.write s)
      else some (2,.move .left)
  else if k<3+(e+1) then
    let i := (k-3)%(e+1)
    if i=0 then some (2,.write s)
      else some (3+(e+1)+(i-1),.write a)
  else if k<3+2*(e+1) then some (3+(k-(3+(e+1)))%(e+1),.move .right)
  else (M ((Coding.fixed Q).dec (k-(3+2*(e+1)))) s).map
    (fun p => (3+2*(e+1)+(Coding.fixed Q).enc p.1,p.2))

lemma transition_eq (M : TM0.Machine Γ Q) (a z sep : Γ) (e : ℕ) (v : ℕ × Γ) :
    transition M a z sep e v=transitionNumeric M a z sep e v := by
  unfold transition transitionNumeric labelCoding
  dsimp only
  split_ifs <;> simp_all [machine]
  all_goals rfl

/-- The actual encoded transition of the finite counter wrapper is uniform. -/
theorem transition_primrec (M : TM0.Machine Γ Q) (a z sep : Γ) :
    Primrec₂ (transition M a z sep) := by
  have hM : Primrec (fun p : Q × Γ => M p.1 p.2) := Primrec.dom_finite _
  have hinput : Primrec (fun p : ℕ × (ℕ × Γ) =>
      M ((Coding.fixed Q).dec (p.2.1-(3+2*(p.1+1)))) p.2.2) := by
    exact hM.comp (show Primrec (fun p : ℕ × (ℕ × Γ) =>
      ((Coding.fixed Q).dec (p.2.1-(3+2*(p.1+1))),p.2.2)) from by fun_prop)
  have hg : Primrec (fun p : (ℕ × (ℕ × Γ)) × (Q × TM0.Stmt Γ) =>
      (3+2*(p.1.1+1)+(Coding.fixed Q).enc p.2.1,p.2.2)) := by fun_prop
  have hmap := Primrec.option_map hinput hg.to₂
  have h : Primrec (fun p : ℕ × (ℕ × Γ) => transitionNumeric M a z sep p.1 p.2) := by
    unfold transitionNumeric
    dsimp only
    refine Primrec.ite (by fun_prop) (by fun_prop) ?_
    refine Primrec.ite (by fun_prop) (by fun_prop) ?_
    exact Primrec.ite (by fun_prop) (by fun_prop) hmap
  exact h.of_eq fun p => (transition_eq M a z sep p.1 p.2).symm

#print axioms normalize_primrec
#print axioms transition_primrec
end Sigma2.SimulatorParameterKernel





