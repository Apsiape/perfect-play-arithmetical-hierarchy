import Sigma2.CompilerBase
import Sigma2.GameTableEffective

/-! Primitive-recursive numeric constructors for the frozen derived syntax.
These identities concern the original codecs. They do not establish the full
presentation-to-game generator or claim a new Primcodable instance for Expr. -/
noncomputable section
namespace Sigma2.CompilerSyntaxCodes
open GameTableEffective

attribute [local fun_prop] Primrec Primrec₂ Primrec.id Primrec.const Primrec.fst Primrec.snd
  Primrec.comp Primrec.succ Primrec.pair
attribute [local fun_prop] nat_pair_primrec node_primrec

def cons (a b : ℕ) : ℕ := Nat.pair (Nat.succ a) b
@[local fun_prop] theorem cons_primrec : Primrec (fun p : ℕ × ℕ => cons p.1 p.2) := by
  unfold cons
  fun_prop

def scalarCode (q : ℚ) : ℕ := node 0 (node (Encodable.encode q) 0)
def labelCode (i : ℕ) : ℕ := node 1 (node i 0)
def addCode (p q : ℕ) : ℕ := node 2 (cons p (cons q 0))
def mulCode (p q : ℕ) : ℕ := node 3 (cons p (cons q 0))
def adjCode (p : ℕ) : ℕ := node 4 (cons p 0)

@[simp] theorem scalar_encode (q : ℚ) : scalarCode q=Encodable.encode (Expr.scalar q) := rfl
@[simp] theorem label_encode (i : ℕ) : labelCode i=Encodable.encode (Expr.label i) := rfl
@[simp] theorem add_encode (p q : Expr) :
    addCode (Encodable.encode p) (Encodable.encode q)=Encodable.encode (Expr.add p q) := rfl
@[simp] theorem mul_encode (p q : Expr) :
    mulCode (Encodable.encode p) (Encodable.encode q)=Encodable.encode (Expr.mul p q) := rfl
@[simp] theorem adj_encode (p : Expr) :
    adjCode (Encodable.encode p)=Encodable.encode (Expr.adj p) := rfl

theorem scalarCode_primrec : Primrec scalarCode := by
  unfold scalarCode
  have henc : Primrec (Encodable.encode : ℚ → ℕ) := Primrec.encode
  fun_prop

theorem labelCode_primrec : Primrec labelCode := by unfold labelCode; fun_prop
theorem addCode_primrec : Primrec (fun p : ℕ × ℕ => addCode p.1 p.2) := by unfold addCode; fun_prop
theorem mulCode_primrec : Primrec (fun p : ℕ × ℕ => mulCode p.1 p.2) := by unfold mulCode; fun_prop
theorem adjCode_primrec : Primrec adjCode := by unfold adjCode; fun_prop

abbrev FieldCodes := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ

def presentationCode (p : FieldCodes) : ℕ :=
  node 0 (node p.1 (node p.2.1 (node p.2.2.1 (node p.2.2.2.1
    (node p.2.2.2.2.1 (node p.2.2.2.2.2.1 (node p.2.2.2.2.2.2 0)))))))

def fields (P : Presentation) : FieldCodes :=
  (Encodable.encode P.types,P.root,Encodable.encode P.transported,
    Encodable.encode P.central,Encodable.encode P.endpoints,Encodable.encode P.zeros,
    Encodable.encode P.linear)

theorem presentationCode_eq_encode (P : Presentation) :
    presentationCode (fields P)=Encodable.encode P := by cases P; rfl

theorem presentationCode_primrec : Primrec presentationCode := by
  unfold presentationCode
  fun_prop

/-- Existing labels retain their original encodings and four-way tags. -/
def typeCode (i : ℕ) : ℕ := node i 0

theorem typeCode_primrec : Primrec typeCode := by unfold typeCode; fun_prop

theorem typeCode_encode :
    typeCode 0=Encodable.encode LabelType.unitary ∧
    typeCode 1=Encodable.encode LabelType.projection ∧
    typeCode 2=Encodable.encode LabelType.positive ∧
    typeCode 3=Encodable.encode LabelType.contraction := by exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms scalar_encode
#print axioms add_encode
#print axioms mul_encode
#print axioms adj_encode
#print axioms scalarCode_primrec
#print axioms labelCode_primrec
#print axioms addCode_primrec
#print axioms mulCode_primrec
#print axioms adjCode_primrec
#print axioms presentationCode_eq_encode
#print axioms presentationCode_primrec
#print axioms typeCode_primrec
#print axioms typeCode_encode
end Sigma2.CompilerSyntaxCodes
