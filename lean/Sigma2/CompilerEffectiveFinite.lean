import Sigma2.CompilerEffectiveCore
noncomputable section
set_option maxHeartbeats 150000
namespace Sigma2.CompilerEffective
open CompilerScaffold
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair
  Computable.option_some Computable.option_casesOn Computable.option_map
  Computable.option_bind Computable.cond Computable.sumInl Computable.sumInr

abbrev NameData := ℕ ⊕ ℕ ⊕ ℕ ⊕ (Word × ℕ × ℕ) ⊕ (Word × Word × Word) ⊕
  (ℕ × ℕ × Bool) ⊕ (ℕ × ℕ × ℕ × ℕ)
def nameEquiv : ProjectionName ≃ NameData where
  toFun
    | .parameter i => .inl i
    | .active g => .inr (.inl g)
    | .frame i => .inr (.inr (.inl i))
    | .graph w k l => .inr (.inr (.inr (.inl (w,k,l))))
    | .triangle u v w => .inr (.inr (.inr (.inr (.inl (u,v,w)))))
    | .binding p i b => .inr (.inr (.inr (.inr (.inr (.inl (p,i,b))))))
    | .joint p k a b => .inr (.inr (.inr (.inr (.inr (.inr (p,k,a,b))))))
  invFun
    | .inl i => .parameter i
    | .inr (.inl g) => .active g
    | .inr (.inr (.inl i)) => .frame i
    | .inr (.inr (.inr (.inl (w,k,l)))) => .graph w k l
    | .inr (.inr (.inr (.inr (.inl (u,v,w))))) => .triangle u v w
    | .inr (.inr (.inr (.inr (.inr (.inl (p,i,b)))))) => .binding p i b
    | .inr (.inr (.inr (.inr (.inr (.inr (p,k,a,b)))))) => .joint p k a b
  left_inv := by intro n; cases n <;> rfl
  right_inv := by
    intro d
    rcases d with i | g | i | ⟨w,k,l⟩ | ⟨u,v,w⟩ | ⟨p,i,b⟩ | ⟨p,k,a,b⟩ <;> rfl

/-- Internal finite names have no external codec in the frozen scaffold. -/
instance namePrimcodable : Primcodable ProjectionName := Primcodable.ofEquiv NameData nameEquiv
@[local fun_prop] theorem name_back : Computable nameEquiv.symm := Primrec.of_equiv_symm.to_comp

abbrev RowData := ℚ × List (ℚ × ProjectionName)
def rowEquiv : RationalRow ≃ RowData where
  toFun r := (r.constant,r.terms)
  invFun r := ⟨r.1,r.2⟩
  left_inv := by intro r; cases r; rfl
  right_inv := by intro r; cases r; rfl
instance rowPrimcodable : Primcodable RationalRow := Primcodable.ofEquiv RowData rowEquiv
@[local fun_prop] theorem row_back : Computable rowEquiv.symm := Primrec.of_equiv_symm.to_comp
@[local fun_prop] theorem row_forward : Computable rowEquiv := Primrec.of_equiv.to_comp

variable {α : Type} [Primcodable α]
@[fun_prop] theorem cparameter (i : α → ℕ) (hi : Computable i) :
    Computable (fun z => ProjectionName.parameter (i z)) := by
  change Computable (fun z => nameEquiv.symm (Sum.inl (i z)))
  fun_prop
@[fun_prop] theorem cactive (g : α → ℕ) (hg : Computable g) :
    Computable (fun z => ProjectionName.active (g z)) := by
  change Computable (fun z => nameEquiv.symm (Sum.inr (Sum.inl (g z))))
  fun_prop
@[fun_prop] theorem cframe (i : α → ℕ) (hi : Computable i) :
    Computable (fun z => ProjectionName.frame (i z)) := by
  change Computable (fun z => nameEquiv.symm (Sum.inr (Sum.inr (Sum.inl (i z)))))
  fun_prop
@[fun_prop] theorem cgraph (w : α → Word) (k : α → ℕ) (l : α → ℕ) (hw : Computable w) (hk : Computable k) (hl : Computable l) :
    Computable (fun z => ProjectionName.graph (w z) (k z) (l z)) := by
  change Computable (fun z => nameEquiv.symm (Sum.inr (Sum.inr (Sum.inr (Sum.inl (w z,k z,l z))))))
  fun_prop
@[fun_prop] theorem ctriangle (u : α → Word) (v : α → Word) (w : α → Word) (hu : Computable u) (hv : Computable v) (hw : Computable w) :
    Computable (fun z => ProjectionName.triangle (u z) (v z) (w z)) := by
  change Computable (fun z => nameEquiv.symm (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (u z,v z,w z)))))))
  fun_prop
@[fun_prop] theorem cbinding (p : α → ℕ) (i : α → ℕ) (b : α → Bool) (hp : Computable p) (hi : Computable i) (hb : Computable b) :
    Computable (fun z => ProjectionName.binding (p z) (i z) (b z)) := by
  change Computable (fun z => nameEquiv.symm (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (p z,i z,b z))))))))
  fun_prop
@[fun_prop] theorem cjoint (p : α → ℕ) (k : α → ℕ) (a : α → ℕ) (b : α → ℕ) (hp : Computable p) (hk : Computable k) (ha : Computable a) (hb : Computable b) :
    Computable (fun z => ProjectionName.joint (p z) (k z) (a z) (b z)) := by
  change Computable (fun z => nameEquiv.symm (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr ((p z,k z,a z,b z)))))))))
  fun_prop

@[fun_prop] theorem crow (ts : α → List (ℚ × ProjectionName)) (c : α → ℚ)
    (hts : Computable ts) (hc : Computable c) :
    Computable (fun a => row (ts a) (c a)) := by
  have h := row_back.comp (hc.pair hts)
  exact h.of_eq (fun a => rfl)
@[fun_prop] theorem cconstant (f : α → RationalRow) (hf : Computable f) :
    Computable (fun a => (f a).constant) := Computable.fst.comp (row_forward.comp hf)
@[fun_prop] theorem cterms (f : α → RationalRow) (hf : Computable f) :
    Computable (fun a => (f a).terms) := Computable.snd.comp (row_forward.comp hf)

@[fun_prop] theorem cone : Computable (fun _ : α => one) := Computable.const _
@[fun_prop] theorem cscalar (q : α → ℚ) (hq : Computable q) :
    Computable (fun a => scalar (q a)) := by unfold scalar; fun_prop
@[fun_prop] theorem catom (i : α → ℕ) (hi : Computable i) :
    Computable (fun a => atom (i a)) := by unfold atom; fun_prop
@[fun_prop] theorem cscale (q : α → ℚ) (p : α → Poly) (hq : Computable q) (hp : Computable p) :
    Computable (fun a => scale (q a) (p a)) := by unfold scale; fun_prop
@[fun_prop] theorem cpsub (p q : α → Poly) (hp : Computable p) (hq : Computable q) :
    Computable (fun a => sub (p a) (q a)) := by unfold sub; fun_prop
@[fun_prop] theorem cpmul (p q : α → Poly) (hp : Computable p) (hq : Computable q) :
    Computable (fun a => mul (p a) (q a)) := by unfold mul; fun_prop
@[fun_prop] theorem cadjWord (w : α → Word) (hw : Computable w) :
    Computable (fun a => adjWord (w a)) := by
  unfold adjWord
  apply clist_map
  · exact Computable.list_reverse.comp hw
  · fun_prop
@[fun_prop] theorem cpadj (p : α → Poly) (hp : Computable p) :
    Computable (fun a => adj (p a)) := by unfold adj; fun_prop
@[fun_prop] theorem cpsum (ps : α → List Poly) (hp : Computable ps) :
    Computable (fun a => sum (ps a)) := Primrec.list_flatten.to_comp.comp hp

@[fun_prop] theorem cwordClosure (w : α → Word) (hw : Computable w) :
    Computable (fun a => wordClosure (w a)) := by unfold wordClosure; fun_prop

theorem wordClosure_computable : Computable wordClosure := cwordClosure id Computable.id

theorem graphRows_computable : Computable (fun z : Word × ℕ => graphRows z.1 z.2) := by
  unfold graphRows
  fun_prop
@[fun_prop] theorem cgraphRows (w : α → Word) (k : α → ℕ) (hw : Computable w) (hk : Computable k) :
    Computable (fun a => graphRows (w a) (k a)) :=
  (graphRows_computable.comp (hw.pair hk)).of_eq (fun a => rfl)

@[fun_prop] theorem ctriangleRow (u v w : α → Word)
    (hu : Computable u) (hv : Computable v) (hw : Computable w) :
    Computable (fun a => triangleRow (u a) (v a) (w a)) := by unfold triangleRow; fun_prop

@[local fun_prop] theorem graphRows_computable₂ : Computable₂ graphRows :=
  graphRows_computable.to₂

theorem wordRows_computable : Computable wordRows := by
  have hc : Computable (fun w : Word =>
      (List.range 3).flatMap (graphRows w) ++
      [triangleRow w [] w,triangleRow [] w w] ++
      (if w.length>1 then [triangleRow (w.take (w.length-1)) (w.drop (w.length-1)) w] else []) ++
      (if w.length=1 then
        let t := w.head?.getD (0,false)
        [triangleRow [t] [(t.1,!t.2)] [],triangleRow [(t.1,!t.2)] [t] []]
      else [])) := by
    have hhead : Computable (fun w : Word => w.head?.getD (0,false)) :=
      Primrec.option_getD.to_comp.comp Primrec.list_head?.to_comp (Computable.const _)
    fun_prop
  apply hc.of_eq
  intro w
  cases w with
  | nil => simp [wordRows]
  | cons t w => cases w <;> simp [wordRows,List.head?]

theorem bindingRows_computable : Computable bindingRows := by unfold bindingRows; fun_prop

theorem polynomialRow_computable : Computable polynomialRow := by unfold polynomialRow; fun_prop

theorem coefficient_computable : Computable (fun z : RationalRow × ProjectionName =>
    coefficient z.1 z.2) := by
  have ht : Computable (fun z : RationalRow × ProjectionName => z.1.terms) :=
    cterms Prod.fst Computable.fst
  have heq : Computable (fun z : (RationalRow × ProjectionName) × (ℚ × ProjectionName) =>
      decide (z.2.2=z.1.2)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.snd.comp Computable.fst)
  have hf := clist_filter (fun z : RationalRow × ProjectionName => z.1.terms)
    (fun z t => decide (t.2=z.2)) ht heq
  have hm := clist_map _ (fun (_ : RationalRow × ProjectionName) (t : ℚ × ProjectionName) => t.1)
    hf (Computable.fst.comp Computable.snd)
  exact crsum _ hm

end Sigma2.CompilerEffective
