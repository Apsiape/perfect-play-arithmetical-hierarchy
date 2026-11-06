import Sigma2.Compiler
import Sigma2.TreeWords

noncomputable section
open scoped BigOperators
namespace Sigma2.Tree

def xCoord : Word → ℕ
  | [] => 0
  | a::w => 2*xCoord w+a.val/2

def yCoord : Word → ℕ
  | [] => 0
  | a::w => 2*yCoord w+a.val%2

def nextX : Word → Word
  | [] => []
  | a::w => if h : a.val<2 then ⟨a.val+2,by omega⟩::w
    else ⟨a.val-2,by omega⟩::nextX w

def nextY : Word → Word
  | [] => []
  | a::w => if h : a.val%2=0 then ⟨a.val+1,by omega⟩::w
    else ⟨a.val-1,by omega⟩::nextY w

structure Coordinates {P} (R : NormalRealization P) where
  ux : Op
  uy : Op
  px : Op
  py : Op
  ux_unitary : TypedAt R.support ux .unitary
  uy_unitary : TypedAt R.support uy .unitary
  px_projection : Projection px
  py_projection : Projection py
  supported : ∀ T ∈ [ux,uy,px,py], R.support*T=T ∧ T*R.support=T
  centralizer : ∀ T ∈ [ux,uy,px,py], Centralizes R.density.op T
  ux_root : ux*R.label P.root=R.label P.root
  uy_root : uy*R.label P.root=R.label P.root
  px_root : px*R.label P.root=R.label P.root
  py_root : py*R.label P.root=R.label P.root
  ux_rec : ∀ b : Fin 2,
    ux*R.creation ⟨b.val,by omega⟩=R.creation ⟨b.val+2,by omega⟩ ∧
    ux*R.creation ⟨b.val+2,by omega⟩=R.creation ⟨b.val,by omega⟩*ux
  uy_rec : ∀ a : Fin 2,
    uy*R.creation ⟨2*a.val,by omega⟩=R.creation ⟨2*a.val+1,by omega⟩ ∧
    uy*R.creation ⟨2*a.val+1,by omega⟩=R.creation ⟨2*a.val,by omega⟩*uy
  px_rec : ∀ b : Fin 2,
    px*R.creation ⟨b.val,by omega⟩=R.creation ⟨b.val,by omega⟩*px ∧
    px*R.creation ⟨b.val+2,by omega⟩=0
  py_rec : ∀ a : Fin 2,
    py*R.creation ⟨2*a.val,by omega⟩=R.creation ⟨2*a.val,by omega⟩*py ∧
    py*R.creation ⟨2*a.val+1,by omega⟩=0

/-- Eqs. (34)-(37), full root multiplicity, not just one chosen eigenvector. -/
theorem coordinate_identification {P} (hP : P.admissible) (R : NormalRealization P)
    (C : Coordinates R) (w : Word) (ξ : H) (hξ : R.label P.root ξ=ξ) :
    C.ux (wordOp R w ξ)=wordOp R (nextX w) ξ ∧
    C.uy (wordOp R w ξ)=wordOp R (nextY w) ξ ∧
    C.px (wordOp R w ξ)=(if xCoord w=0 then wordOp R w ξ else 0) ∧
    C.py (wordOp R w ξ)=(if yCoord w=0 then wordOp R w ξ else 0) := by
  have hr : R.support ξ=ξ := by
    rw [← hξ]
    exact congrArg (fun A : Op => A ξ) (R.label_supported P.root).1
  have root_action (T : Op) (ht : T*R.label P.root=R.label P.root) : T ξ=ξ := by
    have hh := congrArg (fun A : Op => A ξ) ht
    simpa only [mul_apply_eq_comp,hξ] using hh
  induction w with
  | nil =>
    simpa [wordOp,nextX,nextY,xCoord,yCoord,hr] using
      And.intro (root_action C.ux C.ux_root)
        (And.intro (root_action C.uy C.uy_root)
          (And.intro (root_action C.px C.px_root) (root_action C.py C.py_root)))
  | cons a w ih =>
    refine ⟨?_,?_,?_,?_⟩
    · fin_cases a
      · simpa [nextX,wordOp,mul_apply_eq_comp] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.ux_rec 0).1
      · simpa [nextX,wordOp,mul_apply_eq_comp] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.ux_rec 1).1
      · simpa [nextX,wordOp,mul_apply_eq_comp,ih.1] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.ux_rec 0).2
      · simpa [nextX,wordOp,mul_apply_eq_comp,ih.1] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.ux_rec 1).2
    · fin_cases a
      · simpa [nextY,wordOp,mul_apply_eq_comp] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.uy_rec 0).1
      · simpa [nextY,wordOp,mul_apply_eq_comp,ih.2.1] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.uy_rec 0).2
      · simpa [nextY,wordOp,mul_apply_eq_comp] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.uy_rec 1).1
      · simpa [nextY,wordOp,mul_apply_eq_comp,ih.2.1] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.uy_rec 1).2
    · fin_cases a
      · simpa [xCoord,wordOp,mul_apply_eq_comp,ih.2.2.1,apply_ite] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.px_rec 0).1
      · simpa [xCoord,wordOp,mul_apply_eq_comp,ih.2.2.1,apply_ite] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.px_rec 1).1
      · simpa [xCoord,wordOp,mul_apply_eq_comp] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.px_rec 0).2
      · simpa [xCoord,wordOp,mul_apply_eq_comp] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.px_rec 1).2
    · fin_cases a
      · simpa [yCoord,wordOp,mul_apply_eq_comp,ih.2.2.2,apply_ite] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.py_rec 0).1
      · simpa [yCoord,wordOp,mul_apply_eq_comp] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.py_rec 0).2
      · simpa [yCoord,wordOp,mul_apply_eq_comp,ih.2.2.2,apply_ite] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.py_rec 1).1
      · simpa [yCoord,wordOp,mul_apply_eq_comp] using
          congrArg (fun A : Op => A (wordOp R w ξ)) (C.py_rec 1).2

structure Automaton where
  extraSymbols : ℕ
  update : Option (Fin (extraSymbols+3)) → Fin (extraSymbols+3) →
    Fin (extraSymbols+3) → Bool → Fin (extraSymbols+3)
  blank_quiescence : ∀ ε, update (some 1) 1 1 ε=1

abbrev Symbol (M : Automaton) := Fin (M.extraSymbols+3)

def run (M : Automaton) (pulse : ℕ → Bool) : ℕ → ℕ → Symbol M
  | 0,x => if x=0 then 0 else 1
  | t+1,x => M.update (if x=0 then none else some (run M pulse t (x-1)))
      (run M pulse t x) (run M pulse t (x+1)) (pulse t)

structure Tableau {P} (R : NormalRealization P) (C : Coordinates R) (M : Automaton) where
  symbol : Symbol M → Op
  pulse : Op
  projections : ∀ c, Projection (symbol c)
  orthogonal : ∀ c d, c≠d → symbol c*symbol d=0
  partition : ∑ c, symbol c=R.support
  pulse_projection : Projection pulse
  centralizer : (∀ c, Centralizes R.density.op (symbol c)) ∧ Centralizes R.density.op pulse
  supported : (∀ c, R.support*symbol c=symbol c ∧ symbol c*R.support=symbol c) ∧
    R.support*pulse=pulse ∧ pulse*R.support=pulse
  initial_start : symbol 0*C.px*C.py=C.px*C.py
  initial_blank : symbol 1*(R.support-C.px)*C.py=(R.support-C.px)*C.py
  no_halt : symbol 2=0
  transition : ∀ a,
    let lastX := star C.ux*C.px*C.ux
    let lastY := star C.uy*C.py*C.uy
    let L : Option (Symbol M) → Op := fun l => match l with
      | none => C.px
      | some c => C.ux*symbol c*star C.ux*(R.support-C.px)
    let N : Symbol M → Op := fun r => star C.ux*symbol r*C.ux*(R.support-lastX)+
      (if r=1 then lastX else 0)
    (star C.uy*symbol a*C.uy-
      ∑ l, ∑ c, ∑ r, ∑ ε : Bool,
        if M.update l c r ε=a then L l*symbol c*N r*(if ε then pulse else R.support-pulse) else 0)*
      (R.support-lastY)=0


end Sigma2.Tree
