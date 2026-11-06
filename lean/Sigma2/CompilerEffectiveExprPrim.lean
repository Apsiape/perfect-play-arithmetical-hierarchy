import Sigma2.CompilerEffectiveExpr
noncomputable section
set_option linter.unusedSimpArgs false
namespace Sigma2.CompilerEffectiveCoding
open CompilerSyntaxCodes GameTableEffective CompilerEffective
attribute [local irreducible] Nat.pair Encodable.encodeList exprNorm
attribute [local fun_prop] Primrec Primrec₂ Primrec.id Primrec.const Primrec.fst Primrec.snd
  Primrec.comp Primrec.pair Primrec.succ Primrec.option_some Primrec.ite Primrec.unpair
  Primrec.list_length Primrec.option_isSome
  asNat_primrec getUnary_primrec getBinary_primrec pcons pnode
  scalarCode_primrec labelCode_primrec adjCode_primrec addCode_primrec mulCode_primrec
  peqPred peq pite
variable {α β : Type} [Primcodable α] [Primcodable β]

@[local fun_prop] theorem pgetD (f : α → Option β) (g : α → β)
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => (f a).getD (g a)) :=
  Primrec.option_getD.comp hf hg

@[local fun_prop] theorem pmap1 (f : β → α) (hf : Primrec f) :
    Primrec (fun o : Option β => o.map f) := Primrec.option_map₁ hf

def pairOptions (x : Option α) (y : Option β) : Option (α × β) :=
  x.bind (fun a => y.map (fun b => (a,b)))

theorem pairOptions_primrec : Primrec (fun z : Option α × Option β => pairOptions z.1 z.2) := by
  have hb : Primrec (fun z : (Option α × Option β) × α => z.1.2.map (fun b => (z.2,b))) :=
    Primrec.option_map (Primrec.snd.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂
  exact Primrec.option_bind Primrec.fst hb.to₂
attribute [local fun_prop] pairOptions_primrec

def rationalArg (n : ℕ) : Option ℕ :=
  ((asNat n).bind (Encodable.decode (α := ℚ))).map scalarCode

theorem rationalArg_primrec : Primrec rationalArg :=
  (Primrec.option_map₁ scalarCode_primrec).comp
    ((Primrec.option_bind₁ (Primrec.decode (α := ℚ))).comp asNat_primrec)
attribute [local fun_prop] rationalArg_primrec

def previousAt (l : List (Option ℕ)) (k : ℕ) : Option ℕ := l[k]?.getD none
@[local fun_prop] theorem previousAt_primrec :
    Primrec (fun z : List (Option ℕ) × ℕ => previousAt z.1 z.2) :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const none)

def unaryBody (z : List (Option ℕ) × (ℕ × ℕ)) : Option ℕ :=
  if z.2.1=0 then rationalArg z.2.2
  else if z.2.1=1 then (asNat z.2.2).map labelCode
  else if z.2.1=4 then (previousAt z.1 z.2.2).map adjCode
  else none

def binaryBody (z : List (Option ℕ) × (ℕ × ℕ × ℕ)) : Option ℕ :=
  let ps := pairOptions (previousAt z.1 z.2.2.1) (previousAt z.1 z.2.2.2)
  if z.2.1=2 then ps.map (fun p => addCode p.1 p.2)
  else if z.2.1=3 then ps.map (fun p => mulCode p.1 p.2)
  else none

theorem unaryBody_primrec : Primrec unaryBody := by unfold unaryBody; fun_prop
theorem binaryBody_primrec : Primrec binaryBody := by unfold binaryBody; fun_prop

def unaryTable (l : List (Option ℕ)) : Option ℕ :=
  (getUnary l.length).bind (fun z => unaryBody (l,z))
def binaryTable (l : List (Option ℕ)) : Option ℕ :=
  (getBinary l.length).bind (fun z => binaryBody (l,z))

theorem unaryTable_primrec : Primrec unaryTable :=
  Primrec.option_bind (getUnary_primrec.comp Primrec.list_length) unaryBody_primrec.to₂
theorem binaryTable_primrec : Primrec binaryTable :=
  Primrec.option_bind (getBinary_primrec.comp Primrec.list_length) binaryBody_primrec.to₂

def stepTable (l : List (Option ℕ)) : Option (Option ℕ) :=
  some ((unaryTable l).orElse (fun _ => binaryTable l))

theorem stepTable_primrec : Primrec stepTable := by
  exact Primrec.option_some.comp (Primrec.option_orElse.comp unaryTable_primrec binaryTable_primrec)

theorem unaryTable_eq (l : List (Option ℕ)) :
    unaryTable l=unaryNorm l.length (previousAt l) := by
  unfold unaryTable unaryNorm
  cases h : getUnary l.length with
  | none => simp
  | some z =>
    obtain ⟨tag,arg⟩ := z
    simp [unaryBody,rationalArg,Option.map_eq_bind,Option.bind_assoc,Function.comp_def]

theorem binaryTable_eq (l : List (Option ℕ)) :
    binaryTable l=binaryNorm l.length (previousAt l) := by
  unfold binaryTable binaryNorm
  cases h : getBinary l.length with
  | none => simp
  | some z =>
    obtain ⟨tag,p,q⟩ := z
    by_cases ht2 : tag=2 <;> by_cases ht3 : tag=3 <;>
      simp_all [binaryBody,pairOptions,Option.map_eq_bind,Option.bind_assoc]

theorem getUnary_some_eq {n tag arg : ℕ} (h : getUnary n=some (tag,arg)) :
    n=node tag (cons arg 0) := by
  dsimp only [getUnary] at h
  split at h
  next hc =>
    have hz := Option.some.inj h
    have ht := congrArg Prod.fst hz
    have ha := congrArg Prod.snd hz
    dsimp only at ht ha
    simpa only [ht,ha] using hc
  next _ => cases h

theorem getBinary_some_eq {n tag p q : ℕ} (h : getBinary n=some (tag,p,q)) :
    n=node tag (cons p (cons q 0)) := by
  dsimp only [getBinary] at h
  split at h
  next hc =>
    have hz := Option.some.inj h
    have ht := congrArg Prod.fst hz
    have hp := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) hz
    have hq := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) hz
    dsimp only at ht hp hq
    simpa only [ht,hp,hq] using hc
  next _ => cases h

theorem unary_arg_lt {n tag arg : ℕ} (h : getUnary n=some (tag,arg)) : arg<n := by
  rw [getUnary_some_eq h]
  exact lt_of_lt_of_le (cons_left_lt _ _) (node_right_le _ _)

theorem binary_args_lt {n tag p q : ℕ} (h : getBinary n=some (tag,p,q)) : p<n ∧ q<n := by
  rw [getBinary_some_eq h]
  exact ⟨lt_of_lt_of_le (cons_left_lt _ _) (node_right_le _ _),
    lt_of_lt_of_le (cons_left_lt _ _) (le_trans (cons_right_le _ _) (node_right_le _ _))⟩

theorem exprStep_congr (n : ℕ) (f g : ℕ → Option ℕ) (h : ∀ k, k<n → f k=g k) :
    exprStep n f=exprStep n g := by
  have hu : unaryNorm n f=unaryNorm n g := by
    cases hh : getUnary n with
    | none => simp [unaryNorm,hh]
    | some z =>
      obtain ⟨tag,arg⟩ := z
      simp [unaryNorm,hh,h arg (unary_arg_lt hh)]
  have hb : binaryNorm n f=binaryNorm n g := by
    cases hh : getBinary n with
    | none => simp [binaryNorm,hh]
    | some z =>
      obtain ⟨tag,p,q⟩ := z
      have hs := binary_args_lt hh
      simp [binaryNorm,hh,h p hs.1,h q hs.2]
  simp [exprStep,hu,hb]

theorem exprNorm_primrec : Primrec exprNorm := by
  have hg : Primrec (fun z : Unit × List (Option ℕ) => stepTable z.2) :=
    stepTable_primrec.comp Primrec.snd
  have hs := Primrec.nat_strong_rec (fun (_ : Unit) n => exprNorm n) hg.to₂ (by
    intro _ n
    simp only [stepTable,unaryTable_eq,binaryTable_eq,List.length_map,List.length_range]
    apply congrArg some
    change exprStep n (previousAt ((List.range n).map exprNorm))=exprNorm n
    rw [exprStep_congr n _ exprNorm (by intro k hk; simp [previousAt,hk])]
    exact exprStep_agrees n)
  exact hs.comp (Primrec.const ()) Primrec.id

/-- Extends the original derived codec; its encode and decode fields are unchanged. -/
instance exprPrimcodable : Primcodable Expr where
  toEncodable := Sigma2.instEncodableExpr
  prim := (Primrec.nat_iff.mp (Primrec.encode.comp exprNorm_primrec)).of_eq (fun n => by
    unfold exprNorm
    cases Encodable.decode (α := Expr) n <;> rfl)

theorem expr_decoder_computable : Computable (Encodable.decode (α := Expr)) := Primrec.decode.to_comp
theorem expr_validity_computable : Computable (fun n => (Encodable.decode (α := Expr) n).isSome) :=
  Primrec.option_isSome.to_comp.comp expr_decoder_computable
#print axioms exprNorm_primrec
#print axioms exprPrimcodable
#print axioms expr_decoder_computable
#print axioms expr_validity_computable
end Sigma2.CompilerEffectiveCoding