import Sigma2.ReductionPresentationBase
import Sigma2.SimulatorPrimrec
noncomputable section
set_option maxHeartbeats 100000
namespace Sigma2.PresentationCoding
open Reduction Sigma2.Tree
abbrev N (n : ℕ) := Nat.pair 0 n
abbrev C (a b : ℕ) := Nat.pair (a+1) b
abbrev unary (tag x : ℕ) := C (N tag) (C x (N 0))
abbrev binary (tag x y : ℕ) := C (N tag) (C x (C y (N 0)))
lemma label_code (i : ℕ) : Encodable.encode (Expr.label i) = unary 1 (N i) := by rfl
lemma scalar_code (q : ℚ) : Encodable.encode (Expr.scalar q) = unary 0 (N (Encodable.encode q)) := by rfl
lemma add_code (p q : Expr) : Encodable.encode (Expr.add p q) = binary 2 (Encodable.encode p) (Encodable.encode q) := by rfl
lemma mul_code (p q : Expr) : Encodable.encode (Expr.mul p q) = binary 3 (Encodable.encode p) (Encodable.encode q) := by rfl
lemma adj_code (p : Expr) : Encodable.encode (Expr.adj p) = unary 4 (Encodable.encode p) := by rfl
lemma encode_map {α β : Type} [Encodable α] [Encodable β] (f : α → β)
    (h : ∀ a, Encodable.encode (f a)=Encodable.encode a) (xs : List α) :
    Encodable.encode (xs.map f)=Encodable.encode xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih => change Nat.succ (Nat.pair _ _) = Nat.succ (Nat.pair _ _); change Encodable.encodeList (xs.map f) = Encodable.encodeList xs at ih; rw [h,ih]
lemma encode_prod {α β : Type} [Encodable α] [Encodable β] (a : α) (b : β) :
    Encodable.encode (a,b) = Nat.pair (Encodable.encode a) (Encodable.encode b) := by rfl
lemma encode_fin {n : ℕ} (i : Fin n) : Encodable.encode i = i.val := by rfl

attribute [local irreducible] Sigma2.instEncodableExpr Sigma2.instEncodablePresentation
open Sigma2.SimulatorPrimrec
attribute [fun_prop] Primrec.encode Primrec.list_range
variable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
@[fun_prop] theorem npair (f g : α → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => Nat.pair (f a) (g a)) := Primrec₂.natPair.comp hf hg
@[fun_prop] theorem elabel (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun a => Encodable.encode (Expr.label (f a))) := by
  simp only [label_code]; unfold unary C N; fun_prop
@[fun_prop] theorem eadd (f g : α → Expr)
    (hf : Primrec (fun a => Encodable.encode (f a)))
    (hg : Primrec (fun a => Encodable.encode (g a))) :
    Primrec (fun a => Encodable.encode (Expr.add (f a) (g a))) := by
  simp only [add_code]; unfold binary C N; fun_prop
@[fun_prop] theorem emul (f g : α → Expr)
    (hf : Primrec (fun a => Encodable.encode (f a)))
    (hg : Primrec (fun a => Encodable.encode (g a))) :
    Primrec (fun a => Encodable.encode (Expr.mul (f a) (g a))) := by
  simp only [mul_code]; unfold binary C N; fun_prop
@[fun_prop] theorem eadj (f : α → Expr)
    (hf : Primrec (fun a => Encodable.encode (f a))) :
    Primrec (fun a => Encodable.encode (Expr.adj (f a))) := by
  simp only [adj_code]; unfold unary C N; fun_prop
@[fun_prop] theorem lmap (f : α → List β) (g : α × β → σ)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).map (fun b => g (a,b))) := Primrec.list_map hf hg.to₂
@[fun_prop] theorem lflat (f : α → List β) (g : α × β → List σ)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).flatMap (fun b => g (a,b))) := Primrec.list_flatMap hf hg.to₂
@[fun_prop] theorem lfilter (f : α → List β) (g : α × β → Option σ)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a).filterMap (fun b => g (a,b))) := Primrec.listFilterMap hf hg.to₂
@[fun_prop] theorem lcons (f : α → β) (g : α → List β)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a :: g a) := Primrec.list_cons.comp hf hg
@[fun_prop] theorem lappend (f g : α → List β)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a ++ g a) := Primrec.list_append.comp hf hg
@[fun_prop] theorem lget (f : α → List β) (g : α → ℕ)
    (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => (f a)[g a]?) := Primrec.list_getElem?.comp hf hg
lemma enum_values (n : ℕ) :
    (List.ofFn (fun i : Fin n => i)).map Fin.val = List.range n := by
  apply List.ext_getElem <;> simp
lemma fin_flatMap_eq {σ : Type} (n : ℕ) (f : Fin n → List σ) (g : ℕ → List σ)
    (h : ∀ i, f i = g i.val) :
    (List.ofFn (fun i : Fin n => i)).flatMap f = (List.range n).flatMap g := by
  rw [← enum_values n, List.flatMap_map]
  congr 1
  funext i
  exact h i
open Reduction.Syntax

def updateNat (r : RawAutomaton) (l : Option ℕ) (c d : ℕ) (b : Bool) : ℕ :=
  if l=some 1 ∧ c=1 ∧ d=1 then 1 else
    (r.2[(((l.map (fun k => k+1)).getD 0*(r.1+3)+c)*(r.1+3)+d)*2+
      (if b then 1 else 0)]?).getD 1 % (r.1+3)
lemma updateNat_eq (r : RawAutomaton) (l : Option (Fin (r.1+3)))
    (c d : Fin (r.1+3)) (b : Bool) :
    updateNat r (l.map Fin.val) c.val d.val b = ((automatonOfRaw r).update l c d b).val := by
  have hc : c=1 ↔ c.val=1 := by simp [Fin.ext_iff, Fin.val_one]
  have hd : d=1 ↔ d.val=1 := by simp [Fin.ext_iff, Fin.val_one]
  have hl : l=some 1 ↔ l.map Fin.val=some 1 := by
    cases l <;> simp [Fin.ext_iff, Fin.val_one]
  simp only [updateNat, automatonOfRaw, hc, hd, hl]
  split_ifs <;> simp [Option.map_map, Function.comp_def, Fin.val_one]

def transitionNat (r : RawAutomaton) (a : ℕ) : Expr :=
  let syms := List.range (r.1+3)
  let terms := (none::syms.map some).flatMap (fun l => syms.flatMap (fun c =>
    syms.flatMap (fun d => [false,true].filterMap (fun b =>
      if updateNat r l c d b=a then
        some (Expr.mul (mul3 (left l) (sym c) (right d))
          (if b then L 10 else sub I (L 10))) else none))))
  .mul (sub (mul3 (.adj (L 2)) (sym a) (L 2)) (sum terms)) (sub I lastY)
lemma transitionNat_eq (r : RawAutomaton) (a : Symbol (automatonOfRaw r)) :
    transitionNat r a.val = transition (automatonOfRaw r) a := by
  have hi (l : Option (Symbol (automatonOfRaw r))) :
      (List.range (r.1+3)).flatMap (fun c => (List.range (r.1+3)).flatMap (fun d =>
        [false,true].filterMap (fun b => if updateNat r (l.map Fin.val) c d b=a.val then
          some (Expr.mul (mul3 (left (l.map Fin.val)) (sym c) (right d))
            (if b then L 10 else sub I (L 10))) else none))) =
      (List.ofFn (fun c : Symbol (automatonOfRaw r) => c)).flatMap (fun c =>
        (List.ofFn (fun d : Symbol (automatonOfRaw r) => d)).flatMap (fun d =>
        [false,true].filterMap (fun b => if (automatonOfRaw r).update l c d b=a then
          some (Expr.mul (mul3 (left (l.map Fin.val)) (sym c.val) (right d.val))
            (if b then L 10 else sub I (L 10))) else none))) := by
    symm
    apply fin_flatMap_eq
    intro c
    apply fin_flatMap_eq
    intro d
    congr 1
    funext b
    have heq := updateNat_eq r l c d b
    by_cases hc : (automatonOfRaw r).update l c d b = a
    · have hn : updateNat r (l.map Fin.val) c.val d.val b = a.val :=
        heq.trans (congrArg Fin.val hc)
      simp only [hc,hn,ite_true]
    · have hn : ¬ updateNat r (l.map Fin.val) c.val d.val b = a.val :=
        fun h => hc (Fin.ext (heq.symm.trans h))
      simp only [hc,hn,ite_false]
  unfold transitionNat transition
  apply congrArg (fun xs : List Expr => Expr.mul
    (sub (mul3 (Expr.adj (L 2)) (sym a.val) (L 2)) (sum xs)) (sub I lastY))
  simp only [List.flatMap_cons, List.flatMap_map]
  apply congrArg₂ List.append
  · exact hi none
  · symm
    apply fin_flatMap_eq
    intro l
    exact (hi (some l)).symm

@[fun_prop] theorem esub (f g : α → Expr)
    (hf : Primrec (fun a => Encodable.encode (f a)))
    (hg : Primrec (fun a => Encodable.encode (g a))) :
    Primrec (fun a => Encodable.encode (sub (f a) (g a))) := by
  unfold sub neg; fun_prop
@[fun_prop] theorem emul3 (f g h : α → Expr)
    (hf : Primrec (fun a => Encodable.encode (f a)))
    (hg : Primrec (fun a => Encodable.encode (g a)))
    (hh : Primrec (fun a => Encodable.encode (h a))) :
    Primrec (fun a => Encodable.encode (mul3 (f a) (g a) (h a))) := by
  unfold mul3; fun_prop
@[fun_prop] theorem esym (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun a => Encodable.encode (sym (f a))) := by
  unfold sym L; fun_prop
@[fun_prop] theorem eL (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun a => Encodable.encode (L (f a))) := by
  unfold L; fun_prop
@[fun_prop] theorem eite (p : α → Prop) [DecidablePred p] (f g : α → Expr)
    (hp : PrimrecPred p) (hf : Primrec (fun a => Encodable.encode (f a)))
    (hg : Primrec (fun a => Encodable.encode (g a))) :
    Primrec (fun a => Encodable.encode (if p a then f a else g a)) := by
  simp only [apply_ite]; exact Primrec.ite hp hf hg
@[fun_prop] theorem eleft (f : α → Option ℕ) (hf : Primrec f) :
    Primrec (fun a => Encodable.encode (left (f a))) := by
  have hg : Primrec (fun a : α × ℕ => Encodable.encode
      (Expr.mul (mul3 (L 1) (sym a.2) (Expr.adj (L 1))) (sub I (L 3)))) := by fun_prop
  have h := Primrec.option_casesOn hf (Primrec.const (Encodable.encode (L 3))) hg.to₂
  exact h.of_eq (fun a => by cases f a <;> rfl)
@[fun_prop] theorem eright (f : α → ℕ) (hf : Primrec f) :
    Primrec (fun a => Encodable.encode (right (f a))) := by
  unfold right; fun_prop
lemma sum_code (xs : List Expr) :
    Encodable.encode (sum xs) = (xs.map Encodable.encode).foldr (binary 2) (Encodable.encode (Expr.scalar 0)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [sum,List.foldr_cons,add_code,List.map_cons] at *
    exact congrArg (binary 2 (Encodable.encode x)) ih
@[fun_prop] theorem esum (f : α → List Expr)
    (hf : Primrec (fun a => (f a).map Encodable.encode)) :
    Primrec (fun a => Encodable.encode (sum (f a))) := by
  simp only [sum_code]
  have hh : Primrec (fun a : α × (ℕ × ℕ) => binary 2 a.2.1 a.2.2) := by
    unfold binary C N; fun_prop
  exact Primrec.list_foldr hf (Primrec.const _) hh.to₂
@[fun_prop] theorem pupd (r : α → RawAutomaton) (l : α → Option ℕ)
    (c d : α → ℕ) (b : α → Bool) (hr : Primrec r) (hl : Primrec l)
    (hc : Primrec c) (hd : Primrec d) (hb : Primrec b) :
    Primrec (fun a => updateNat (r a) (l a) (c a) (d a) (b a)) := by
  unfold updateNat; fun_prop
attribute [local irreducible] updateNat Reduction.Syntax.L Reduction.Syntax.sym Reduction.Syntax.left Reduction.Syntax.right Reduction.Syntax.sub Reduction.Syntax.mul3
lemma transitionNat_primrec : Primrec (fun p : RawAutomaton × ℕ => Encodable.encode (transitionNat p.1 p.2)) := by
  unfold transitionNat
  apply emul
  · apply esub
    · fun_prop
    · apply esum
      simp only [List.map_flatMap,List.map_filterMap,Function.comp_def]
      simp only [Option.map_ite,Option.map_some,Option.map_none]
      have ht : Primrec (fun z : ((((RawAutomaton × ℕ) × Option ℕ) × ℕ) × ℕ) × Bool =>
          if updateNat z.1.1.1.1.1 z.1.1.1.2 z.1.1.2 z.1.2 z.2 = z.1.1.1.1.2 then
            some (Encodable.encode (Expr.mul
              (mul3 (left z.1.1.1.2) (sym z.1.1.2) (right z.1.2))
              (if z.2 then L 10 else sub I (L 10)))) else none) := by
        apply Primrec.ite
        · apply Sigma2.SimulatorPrimrec.peq
          · apply pupd <;> fun_prop
          · fun_prop
        · apply Primrec.option_some.comp
          apply emul
          · apply emul3
            · apply eleft; fun_prop
            · apply esym; fun_prop
            · apply eright; fun_prop
          · apply eite
            · apply Sigma2.SimulatorPrimrec.peq <;> fun_prop
            · exact Primrec.const _
            · exact Primrec.const _
        · exact Primrec.const _
      have h3 : Primrec (fun z : (((RawAutomaton × ℕ) × Option ℕ) × ℕ) × ℕ =>
          [false,true].filterMap (fun b =>
          if updateNat z.1.1.1.1 z.1.1.2 z.1.2 z.2 b = z.1.1.1.2 then
            some (Encodable.encode (Expr.mul (mul3 (left z.1.1.2) (sym z.1.2) (right z.2))
              (if b then L 10 else sub I (L 10)))) else none)) :=
        Primrec.listFilterMap (Primrec.const _) ht.to₂
      have h2 : Primrec (fun z : ((RawAutomaton × ℕ) × Option ℕ) × ℕ =>
          (List.range (z.1.1.1.1+3)).flatMap (fun d =>
          [false,true].filterMap (fun b =>
          if updateNat z.1.1.1 z.1.2 z.2 d b = z.1.1.2 then
            some (Encodable.encode (Expr.mul (mul3 (left z.1.2) (sym z.2) (right d))
              (if b then L 10 else sub I (L 10)))) else none))) := by
        apply Primrec.list_flatMap
        · fun_prop
        · exact h3.to₂
      have h1 : Primrec (fun z : (RawAutomaton × ℕ) × Option ℕ =>
          (List.range (z.1.1.1+3)).flatMap (fun c =>
          (List.range (z.1.1.1+3)).flatMap (fun d =>
          [false,true].filterMap (fun b =>
          if updateNat z.1.1 z.2 c d b = z.1.2 then
            some (Encodable.encode (Expr.mul (mul3 (left z.2) (sym c) (right d))
              (if b then L 10 else sub I (L 10)))) else none)))) := by
        apply Primrec.list_flatMap
        · fun_prop
        · exact h2.to₂
      apply Primrec.list_flatMap
      · apply lcons
        · exact Primrec.const _
        · apply Primrec.list_map
          · fun_prop
          · exact (Primrec.option_some.comp Primrec.snd).to₂
      · exact h1.to₂
  · exact Primrec.const _
end Sigma2.PresentationCoding

