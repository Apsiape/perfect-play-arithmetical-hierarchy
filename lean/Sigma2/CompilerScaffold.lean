import Sigma2.RowGame
import Sigma2.GameTable
import Sigma2.CompilerSyntaxCodes
import Sigma2.PresentationSerialize

/-! Concrete K1 syntax. Internal names are finite syntax, not a replacement
codec. `codeMap` uses the frozen Presentation decoder and GameTable serializer.
No correctness or computability is assumed by this module. -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace Sigma2.CompilerScaffold
open Compiler

abbrev Token := ℕ × Bool
abbrev Word := List Token
abbrev Poly := List (ℚ × Word)

def one : Poly := [(1,[])]
def scalar (q : ℚ) : Poly := [(q,[])]
def atom (i : ℕ) : Poly := [(1,[(i,false)])]
def scale (q : ℚ) (p : Poly) : Poly := p.map (fun t => (q*t.1,t.2))
def sub (p q : Poly) : Poly := p ++ scale (-1) q
def mul (p q : Poly) : Poly := p.flatMap (fun t => q.map (fun u => (t.1*u.1,t.2++u.2)))
def adjWord (w : Word) : Word := w.reverse.map (fun t => (t.1,!t.2))
def adj (p : Poly) : Poly := p.map (fun t => (t.1,adjWord t.2))
def sum (ps : List Poly) : Poly := ps.flatten

/-- Corner numbering: source 0, then four magic corners for each bridge. -/
def cornerIndex (r : ℕ) : ℕ := if r=0 then 0 else 1+4*(r-1)
def corner (i : ℕ) : Poly := scale (1/2) (one ++ atom i)
def e (r : ℕ) : Poly := corner (cornerIndex r)
def magic (g : ℕ) : Poly := sum ((List.range 4).map (fun k => corner (1+4*g+k)))
def activity (g : ℕ) : Poly := e g ++ magic g
/-- 17 corner reflections followed by the 8 calibrated positive-axis parameters. -/
def axisParameter (g k : ℕ) : Poly := corner (17+2*g+k)
def axis (g k : ℕ) : Poly := atom (25+2*g+k)

def encodingCount (P : Presentation) : ℕ :=
  (P.types.map (fun t => if t=LabelType.contraction then 2 else 1)).sum
def encodingOffset (P : Presentation) (i : ℕ) : ℕ :=
  ((P.types.take i).map (fun t => if t=LabelType.contraction then 2 else 1)).sum
/-- All labels are transported, which includes the root and every endpoint label. -/
def copyAtom (P : Presentation) (r l : ℕ) : Poly := atom (33+r*encodingCount P+l)
def blockAtom (P : Presentation) (g l : ℕ) : Poly := atom (33+5*encodingCount P+g*encodingCount P+l)
def creation (P : Presentation) (a : ℕ) : Poly :=
  scale (1/2) (atom (33+9*encodingCount P+2*a) ++ atom (34+9*encodingCount P+2*a))

def labelCopy (P : Presentation) (r i : ℕ) : Poly :=
  let u := copyAtom P r (encodingOffset P i)
  let v := copyAtom P r (encodingOffset P i+1)
  mul (e r) (match P.types[i]?.getD .unitary with
    | .unitary => u
    | .projection => scale (1/2) (one ++ u)
    | .positive => scale (1/4) (scalar 2 ++ u ++ adj u)
    | .contraction => scale (1/2) (u ++ v))

def expression (P : Presentation) (r : ℕ) : Expr → Poly
  | .scalar q => scale q (e r)
  | .label i => labelCopy P r i
  | .add p q => expression P r p ++ expression P r q
  | .mul p q => mul (expression P r p) (expression P r q)
  | .adj p => adj (expression P r p)

def transportTerm (P : Presentation) (g l k : ℕ) : Poly :=
  let x := if k/2=0 then one else axis g 0
  let z := if k%2=0 then one else axis g 1
  let t := mul x z
  mul (mul t (mul (e (g+1)) (copyAtom P (g+1) l))) (adj t)

def structuralPolynomials (P : Presentation) : List Poly :=
  [sub (sum ((List.range 17).map corner)) one] ++
  (List.range 25).map (fun i => sub (mul (atom i) (atom i)) one) ++
  (List.range 4).flatMap (fun g => (List.range 2).map (fun k =>
    sub (axis g k) (one ++ scale (-2) (magic g) ++ scale 2 (axisParameter g k)))) ++
  (List.range 5).flatMap (fun r => (List.range (encodingCount P)).map (fun l =>
    mul (sub (copyAtom P r l) one) (sub one (e r)))) ++
  (List.range 5).flatMap (fun r => (List.range P.types.length).filterMap (fun i =>
    if P.types[i]?=some .projection then
      some (sub (mul (copyAtom P r (encodingOffset P i))
        (copyAtom P r (encodingOffset P i))) one) else none)) ++
  (List.range 4).flatMap (fun g => (List.range (encodingCount P)).map (fun l =>
    sub (blockAtom P g l) (sub one (activity g) ++
      mul (e g) (copyAtom P g l) ++
      sum ((List.range 4).map (transportTerm P g l))))) ++
  (List.range 4).map (fun a => sub (creation P a)
    (mul (mul (e 4) (creation P a)) (e 0)))

/-- Exactly the residual order of Compiler.applicationResiduals. -/
def applicationPolynomials (P : Presentation) : List Poly :=
  (List.range 4).flatMap (fun a => (List.range 4).map (fun b =>
    sub (mul (adj (creation P a)) (creation P b)) (if a=b then e 0 else []))) ++
  [sub (sum ((List.range 4).map (fun a => mul (creation P a) (adj (creation P a)))))
    (sub (e 4) (labelCopy P 4 P.root))] ++
  P.central.map (expression P 0) ++
  P.endpoints.map (fun r => sub (mul (expression P 4 r.1) (creation P r.2.1.val))
    (mul (creation P r.2.2.1.val) (expression P 0 r.2.2.2))) ++
  P.zeros.map (fun r => mul (expression P 4 r.1) (creation P r.2.val)) ++
  P.linear.map (fun row => sum (row.map (fun r =>
    mul (mul (expression P 4 r.1) (creation P r.2.1.val)) (expression P 0 r.2.2))))

attribute [local irreducible] structuralPolynomials applicationPolynomials

def polynomials (P : Presentation) := structuralPolynomials P ++ applicationPolynomials P
/-- Redundant finite prefix closure avoids any word equality oracle. -/
def wordClosure (w : Word) : List Word :=
  (List.range (w.length+1)).map (fun n => w.take n) ++
  w.flatMap (fun t => [[t],[(t.1,!t.2)]])
def words (P : Presentation) : List Word :=
  ([] :: ((polynomials P).flatMap (fun p => p.flatMap (fun t => wordClosure t.2)))).dedup

attribute [local irreducible] words

def pairs : List (ℕ × ℕ) := [(0,1),(0,2),(1,2)]
inductive ProjectionName where
  | parameter (i : ℕ)
  | active (g : ℕ)
  | frame (i : ℕ)
  | graph (w : Word) (pair : ℕ) (part : ℕ)
  | triangle (u v w : Word)
  | binding (p i : ℕ) (complement : Bool)
  | joint (p pair a b : ℕ)
  deriving DecidableEq, Repr
open ProjectionName

/-- A row means constant I + sum coefficient * named projection = 0. -/
structure RationalRow where
  constant : ℚ := 0
  terms : List (ℚ × ProjectionName)
  deriving Repr

def row (xs : List (ℚ × ProjectionName)) (c : ℚ := 0) : RationalRow := ⟨c,xs⟩
def graphRows (w : Word) (k : ℕ) : List RationalRow :=
  let ij := pairs[k]?.getD (0,1)
  [row [(1,.graph w k 0),(1,.graph w k 1),(-1,.frame ij.1),(-1,.frame ij.2)],
   row [(1,.graph w k 2),(1,.graph w k 3),(-1,.frame ij.1),(-1,.frame ij.2)],
   row [(5,.graph w k 2),(-2,.frame ij.1),(1,.frame ij.2),(-4,.graph w k 0)]]
def triangleRow (u v w : Word) : RationalRow :=
  row [(3,.triangle u v w),(-2,.graph u 0 0),(-2,.graph v 2 0),(-2,.graph w 1 0)] 1

def wordRows (w : Word) : List RationalRow :=
  (List.range 3).flatMap (graphRows w) ++
  [triangleRow w [] w,triangleRow [] w w] ++
  (if w.length>1 then [triangleRow (w.take (w.length-1)) (w.drop (w.length-1)) w] else []) ++
  (match w with
    | [t] => [triangleRow [t] [(t.1,!t.2)] [],triangleRow [(t.1,!t.2)] [t] []]
    | _ => [])

def bindingRows (p : ℕ) : List RationalRow :=
  (List.range 3).map (fun i => row [(1,.binding p i false),(1,.binding p i true),(-1,.frame i)]) ++
  [row (((List.range 3).map (fun i => (1,.binding p i false))) ++ [(-1,.parameter p)]),
   row (((List.range 3).map (fun i => (1,.binding p i true))) ++ [(1,.parameter p)]) (-1)] ++
  (List.range 3).flatMap (fun k =>
    let ij := pairs[k]?.getD (0,1)
    [row [(1,.joint p k 1 1),(1,.joint p k 1 0),(-1,.binding p ij.1 false),(-1,.binding p ij.2 false)],
     row [(1,.joint p k 0 0),(1,.joint p k 0 1),(-1,.binding p ij.1 true),(-1,.binding p ij.2 true)],
     row [(1,.joint p k 1 1),(1,.joint p k 0 1),(-1,.graph [] k 0)],
     row [(1,.graph [(p,false)] k 0),(-1,.joint p k 1 1),(-1,.joint p k 0 0)]])

def polynomialRow (p : Poly) : RationalRow :=
  let c := (p.map Prod.fst).sum
  row (p.map (fun t => (2*t.1,.graph t.2 0 0)) ++ [(-c,.frame 0),(-c,.frame 1)])

attribute [local irreducible] graphRows wordRows bindingRows polynomialRow

/-- The finite row list: scalar frame, parameter binding, graph products,
structural equations, then the approximate application equations. -/

def rowList (P : Presentation) : List RationalRow :=
  [row [(1,.frame 0),(1,.frame 1),(1,.frame 2)] (-1),triangleRow [] [] []] ++
  (List.range 25).flatMap bindingRows ++
  (words P).flatMap wordRows ++
  (List.range 4).map (fun g => row ([(1,.active g),(-1,.parameter (cornerIndex g))] ++
    (List.range 4).map (fun k => (-1,.parameter (1+4*g+k))))) ++
  (polynomials P).map polynomialRow

attribute [local irreducible] rowList

/-- Include every row occurrence and every refinement label explicitly. -/

def names (P : Presentation) : List ProjectionName :=
  ((List.range 25).map ProjectionName.parameter ++
    (List.range 4).map ProjectionName.active ++
    (List.range 3).map ProjectionName.frame ++
    (List.range 3).map (fun k => ProjectionName.graph [] k 0) ++
    (List.range 4).flatMap (fun g => (List.range (encodingCount P)).map (fun l =>
      ProjectionName.graph [(33+5*encodingCount P+g*encodingCount P+l,false)] 0 0)) ++
    (rowList P).flatMap (fun (r : RationalRow) => r.terms.map Prod.snd)).dedup

attribute [local irreducible] names

def refinementLabel (P : Presentation) (g k : ℕ) : ProjectionName :=
  if k<3 then .frame k else if k<6 then .graph [] (k-3) 0
  else .graph [(33+5*encodingCount P+g*encodingCount P+(k-6),false)] 0 0

def refinementCount (P : Presentation) : ℕ := 4*(6+encodingCount P)
attribute [local irreducible] refinementCount

def scenario (P : Presentation) : Scenario where
  questionsA := (names P).length+20+refinementCount P
  questionsB := (names P).length+20+refinementCount P
  answersA := 11
  answersB := 11

inductive Question where
  | binary (p : ProjectionName)
  | fms (g x : ℕ)
  | refinement (g k : ℕ)
  | padding
  deriving DecidableEq, Repr

def question (P : Presentation) (x : ℕ) : Question :=
  let n := (names P).length
  if x<n then .binary ((names P)[x]?.getD (.frame 0))
  else if x<n+20 then .fms ((x-n)/5) ((x-n)%5)
  else if x<n+20+refinementCount P then
    .refinement ((x-n-20)/(6+encodingCount P)) ((x-n-20)%(6+encodingCount P))
  else .padding

def valid : Question → ℕ → Bool
  | .binary _,a => decide (a<2)
  | .fms _ _,a => decide (a<6)
  | .refinement _ _,a => decide (a<12)
  | .padding,a => decide (a=0)

/-- All conditional activity, flags, chosen magic corners and calibrated axes,
including coarse events rather than a single arbitrarily chosen outcome. -/
def fmsBinding (alice : Bool) (g x : ℕ) (p : ProjectionName) (a b : ℕ) : Bool :=
  (if p=.active g then decide ((a<5) ↔ b=1) else true) &&
  (if x<3 ∧ p=.parameter (cornerIndex g) then decide ((a=0) ↔ b=1) else true) &&
  (List.range 4).all (fun k =>
    if p=.parameter (1+4*g+k) then
      if alice then
        let q := if k=0 then 4 else 3
        let ans := if k=0 then 2 else k+1
        if x=q then decide ((a=ans) ↔ b=1) else true
      else if x=0 then decide ((a=k+1) ↔ b=1) else true
    else true) &&
  (List.range 2).all (fun k =>
    if p=.parameter (17+2*g+k) then
      let q := if alice then (if k=0 then 1 else 0) else 1
      let j := if alice then 1 else if k=0 then 1 else 0
      if x=q then decide ((0<a ∧ a<5 ∧ cellSign false (a-1) j=false) ↔ b=1) else true
    else true)

def directed (P : Presentation) (alice : Bool) (q p : Question) (a b : ℕ) : Bool :=
  match q,p with
  | .fms g x,.binary n => fmsBinding alice g x n a b
  | .refinement g k,.binary n =>
      if n=refinementLabel P g k then decide ((a%2=1) ↔ b=1) else true
  | .refinement g _,.fms h y =>
      if g=h ∧ y ∈ [0,3,4] then
        if alice then conditionalFmsRule 3 y (a/2) b
        else conditionalFmsRule y 3 b (a/2)
      else true
  | _,_ => true

def rule (P : Presentation) (q p : Question) (a b : ℕ) : Bool :=
  valid q a && valid p b &&
  (match q,p with
    | .binary n,.binary m => if n=m then decide (a=b) else true
    | .fms g x,.fms h y => if g=h then conditionalFmsRule x y a b else true
    | _,_ => true) &&
  directed P true q p a b && directed P false p q b a

def preGame (P : Presentation) : Game where
  scenario := scenario P
  distribution := fun _ _ => 1 / (((scenario P).questionsA+1 : ℕ) *
    ((scenario P).questionsB+1 : ℕ) : ℕ)
  distribution_nonneg := by intro x y; positivity
  distribution_sum := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    push_cast
    field_simp
  accepts := fun x y a b => rule P (question P x.val) (question P y.val) a.val b.val

def event (P : Presentation) (i : Fin (names P).length) : NamedEvent (scenario P) where
  x := ⟨i.val,by have := i.isLt; dsimp [scenario]; omega⟩
  y := ⟨i.val,by have := i.isLt; dsimp [scenario]; omega⟩
  a := ⟨1,by change 1<12; decide⟩
  b := ⟨1,by change 1<12; decide⟩

def coefficient (r : RationalRow) (n : ProjectionName) : ℚ :=
  ((r.terms.filter (fun t => t.2=n)).map Prod.fst).sum

def rows (P : Presentation) : Rows (scenario P) where
  count := (names P).length
  event := event P
  rowCount := (rowList P).length
  constant := fun r => ((rowList P)[r.val]'r.isLt).constant
  coefficient := fun r i => coefficient ((rowList P)[r.val]'r.isLt) ((names P)[i.val]'i.isLt)

/-- Stable decoded-game interface. The Boolean row extension is the proved
Lemma 4.3 construction; this definition supplies its actual input. -/
def finalGame (P : Presentation) : Game := RowGame.game (preGame P) (rows P)
def codeFor (P : Presentation) : ℕ := GameTable.code (finalGame P)
/-- Invalid Presentation codes return 0. No alternate presentation codec. -/
def codeMap (n : ℕ) : ℕ :=
  match Encodable.decode (α := Presentation) n with
  | none => 0
  | some P => codeFor P

theorem decode_codeFor (P : Presentation) : decodeGame (codeFor P)=some (finalGame P) :=
  GameTable.decode_code _
theorem codeMap_encode (P : Presentation) : codeMap (Encodable.encode P)=codeFor P := by
  simp [codeMap,Encodable.encodek]
theorem decode_codeMap (n : ℕ) (P : Presentation)
    (h : Encodable.decode (α := Presentation) n=some P) :
    decodeGame (codeMap n)=some (finalGame P) := by
  simp only [codeMap,h]
  exact decode_codeFor P

theorem application_count (P : Presentation) :
    (applicationPolynomials P).length=17+P.central.length+P.endpoints.length+
      P.zeros.length+P.linear.length := by
  simp [applicationPolynomials,List.length_flatMap]
  omega

/-- The actual numbered conditional FMS questions and six retained answers. -/
def fmsInstance (P : Presentation) (g : Fin 4) : FMSInstance (scenario P) where
  qA x := ⟨(names P).length+5*g.val+x.val,by
    have := g.isLt; have := x.isLt; dsimp [scenario]; omega⟩
  qB x := ⟨(names P).length+5*g.val+x.val,by
    have := g.isLt; have := x.isLt; dsimp [scenario]; omega⟩
  aA a := ⟨a.val,by change a.val<12; have := a.isLt; omega⟩
  aB a := ⟨a.val,by change a.val<12; have := a.isLt; omega⟩
  qA_injective := by
    intro x y h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change (names P).length+5*g.val+x.val=(names P).length+5*g.val+y.val at hv
    omega
  qB_injective := by
    intro x y h
    apply Fin.ext
    have hv := congrArg Fin.val h
    change (names P).length+5*g.val+x.val=(names P).length+5*g.val+y.val at hv
    omega
  aA_injective := by intro x y h; exact Fin.ext (congrArg (fun z : AA (scenario P) => z.val) h)
  aB_injective := by intro x y h; exact Fin.ext (congrArg (fun z : BB (scenario P) => z.val) h)

theorem question_fms (P : Presentation) (g : Fin 4) (x : Fin 5) :
    question P ((names P).length+5*g.val+x.val)=.fms g.val x.val := by
  have hg := g.isLt
  have hx := x.isLt
  simp only [question]
  rw [if_neg (by omega),if_pos (by omega)]
  congr 1 <;> omega

theorem pre_fms_rule (P : Presentation) (g : Fin 4) (x y : Fin 5) (a b : Fin 6) :
    (preGame P).accepts ((fmsInstance P g).qA x) ((fmsInstance P g).qB y)
      ((fmsInstance P g).aA a) ((fmsInstance P g).aB b)=
        conditionalFmsRule x.val y.val a.val b.val := by
  change rule P (question P ((names P).length+5*g.val+x.val))
    (question P ((names P).length+5*g.val+y.val)) a.val b.val=_
  rw [question_fms,question_fms]
  simp [rule,valid,directed,a.isLt,b.isLt]

theorem pre_distribution_positive (P : Presentation) (x y) :
    0 < (preGame P).distribution x y := by dsimp [preGame]; positivity

/-- First K2 step: every retained concrete rejection has zero probability. -/
theorem pre_rejected_probability (P : Presentation)
    (S : NormalStrategy (scenario P)) (hS : Perfect (preGame P) S)
    (x y a b) (h : (preGame P).accepts x y a b=false) : S.probability x y a b=0 := by
  change loss (preGame P) S=0 at hS
  have hh := Preliminaries.losing_event_le_loss (preGame P) S x y a b
  simp only [h,Bool.false_eq_true,ite_false,hS] at hh
  have hd : (0:ℝ)<((preGame P).distribution x y:ℝ) := by
    exact_mod_cast pre_distribution_positive P x y
  have hn := Preliminaries.probability_nonnegative S x y a b
  apply le_antisymm _ hn
  by_contra hp
  exact (not_lt_of_ge hh) (mul_pos hd (lt_of_not_ge hp))

theorem final_retains_pre_rejection (P : Presentation) (x y a b)
    (h : (preGame P).accepts x y a b=false) :
    (finalGame P).accepts ((RowGame.embedding (preGame P) (rows P)).qA x)
      ((RowGame.embedding (preGame P) (rows P)).qB y)
      ((RowGame.embedding (preGame P) (rows P)).aA a)
      ((RowGame.embedding (preGame P) (rows P)).aB b)=false :=
  RowGame.retains_losing _ _ _ _ _ _ (ne_of_gt (pre_distribution_positive P x y)) h

theorem names_nodup (P : Presentation) : (names P).Nodup := by
  unfold names
  exact List.nodup_dedup _

/-- Honest scaffold's finite scalar density, before tensoring with the input. -/
def cornerWeight (i : Fin 17) : ℚ := (2:ℚ)^((i.val+3)/4)/121

theorem cornerWeight_positive (i : Fin 17) : 0<cornerWeight i := by
  dsimp [cornerWeight]; positivity

theorem cornerWeight_sum : ∑ i : Fin 17,cornerWeight i=1 := by
  norm_num [Fin.sum_univ_succ,cornerWeight]

/-- No rational-row occurrence is silently dropped by the event dictionary. -/
theorem row_name_mem (P : Presentation) (r : RationalRow) (hr : r ∈ rowList P)
    (n : ProjectionName) (hn : n ∈ r.terms.map Prod.snd) : n ∈ names P := by
  simp only [names,List.mem_dedup,List.mem_append]
  right
  exact List.mem_flatMap.mpr ⟨r,hr,hn⟩

end Sigma2.CompilerScaffold
