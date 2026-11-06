import Sigma2.PresentationCoding
noncomputable section
set_option maxHeartbeats 100000
namespace Sigma2.PresentationCoding
open Reduction Sigma2.Tree Reduction.Syntax
attribute [local irreducible] Sigma2.instEncodableExpr Sigma2.instEncodableLabelType Nat.pair Encodable.encodeList
variable {α β : Type} [Primcodable α] [Primcodable β]
def recordCode (types root transported central endpoints zeros linear : ℕ) : ℕ :=
  C (N 0) (C (N types) (C (N root) (C (N transported) (C (N central)
    (C (N endpoints) (C (N zeros) (C (N linear) (N 0))))))))
lemma record_code (P : Presentation) : Encodable.encode P =
    recordCode (Encodable.encode P.types) P.root (Encodable.encode P.transported)
      (Encodable.encode P.central) (Encodable.encode P.endpoints)
      (Encodable.encode P.zeros) (Encodable.encode P.linear) := by cases P; rfl
attribute [local irreducible] Sigma2.instEncodablePresentation
@[fun_prop] theorem elist {τ : Type} [Encodable τ] (f : α → List τ)
    (hf : Primrec (fun a => (f a).map Encodable.encode)) :
    Primrec (fun a => Encodable.encode (f a)) :=
  (Primrec.encode.comp hf).of_eq (fun a => encode_map (α := τ) (β := ℕ) (@Encodable.encode τ _) (fun _ => rfl) (f a))
@[fun_prop] theorem lrep (f : α → ℕ) (g : α → β) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => List.replicate (f a) (g a)) := by
  have h := Primrec.list_map (Primrec.list_range.comp hf) (hg.comp Primrec.fst).to₂
  exact h.of_eq (fun a => by simp)
lemma fin_map_eq {σ : Type} (n : ℕ) (f : Fin n → σ) (g : ℕ → σ)
    (h : ∀ i, f i = g i.val) :
    (List.ofFn (fun i : Fin n => i)).map f = (List.range n).map g := by
  rw [← enum_values n,List.map_map]
  congr 1
  funext i
  exact h i

def centralNat (r : RawAutomaton) : List Expr :=
  let syms := List.range (r.1+3)
  [sub (Expr.mul (L 1) (L 0)) (L 0),sub (Expr.mul (L 2) (L 0)) (L 0),
   sub (Expr.mul (L 3) (L 0)) (L 0),sub (Expr.mul (L 4) (L 0)) (L 0),
   sub (Expr.mul (L 5) (L 0)) (L 0),sub (Expr.mul (L 6) (L 0)) (L 0),
   sub (Expr.mul (L 8) (L 9)) (mul3 (L 7) (L 9) (L 8)),
   Expr.mul (sub (L 5) I) (L 10),
   sub (Expr.mul (L 11) (sub (L 5) I)) (Expr.mul (.scalar (1/2)) (Expr.mul (L 6) (sub I (L 10)))),
   sub (mul3 (sym 0) (L 3) (L 4)) (Expr.mul (L 3) (L 4)),
   sub (mul3 (sym 1) (sub I (L 3)) (L 4)) (Expr.mul (sub I (L 3)) (L 4)),
   sym 2,sub (sum (syms.map sym)) I] ++
  ([0,1,2,3,4,5,6,8,9,10,11] ++ syms.map (fun c => 12+c)).map (fun i => comm (L 7) (L i)) ++
  syms.map (transitionNat r)
lemma centralNat_eq (r : RawAutomaton) :
    centralNat r = (applicationPresentation (automatonOfRaw r)).central := by
  have hs := fin_map_eq (r.1+3) (fun c => sym c.val) sym (fun _ => rfl)
  have hl := fin_map_eq (r.1+3) (fun c => 12+c.val) (fun c => 12+c) (fun _ => rfl)
  have ht := fin_map_eq (r.1+3) (transition (automatonOfRaw r)) (transitionNat r)
    (fun a => (transitionNat_eq r a).symm)
  dsimp only [applicationPresentation,centralNat]
  dsimp only [automatonOfRaw] at *
  rw [hs,hl,ht]
@[fun_prop] theorem ecomm (f g : α → Expr)
    (hf : Primrec (fun a => Encodable.encode (f a)))
    (hg : Primrec (fun a => Encodable.encode (g a))) :
    Primrec (fun a => Encodable.encode (Reduction.Syntax.comm (f a) (g a))) := by
  unfold Reduction.Syntax.comm; fun_prop
@[fun_prop] theorem ptransition (r : α → RawAutomaton) (a : α → ℕ)
    (hr : Primrec r) (ha : Primrec a) :
    Primrec (fun x => Encodable.encode (transitionNat (r x) (a x))) :=
  transitionNat_primrec.comp (hr.pair ha)
attribute [local irreducible] applicationPresentation automatonOfRaw
lemma central_code_primrec : Primrec (fun r : RawAutomaton => Encodable.encode (centralNat r)) := by
  have hp : Primrec (fun r : RawAutomaton => Encodable.encode
      (sub (sum ((List.range (r.1+3)).map sym)) I)) := by
    apply esub
    · apply esum
      simp only [List.map_map,Function.comp_def]
      apply Primrec.list_map
      · fun_prop
      · exact (esym (fun z : RawAutomaton × ℕ => z.2) Primrec.snd).to₂
    · exact Primrec.const _
  have hm : Primrec (fun r : RawAutomaton => (List.range (r.1+3)).map
      (fun c => Encodable.encode (Reduction.Syntax.comm (L 7) (L (12+c))))) := by
    apply Primrec.list_map
    · fun_prop
    · have h : Primrec (fun z : RawAutomaton × ℕ =>
          Encodable.encode (Reduction.Syntax.comm (L 7) (L (12+z.2)))) := by fun_prop
      exact h.to₂
  have ht : Primrec (fun r : RawAutomaton => (List.range (r.1+3)).map
      (fun c => Encodable.encode (transitionNat r c))) := by
    apply Primrec.list_map
    · fun_prop
    · exact transitionNat_primrec.to₂
  apply elist
  unfold centralNat
  simp only [List.map_append,List.map_map,List.map_cons,List.map_nil,Function.comp_def]
  fun_prop
lemma types_code_primrec : Primrec (fun r : RawAutomaton =>
    Encodable.encode (applicationPresentation (automatonOfRaw r)).types) := by
  apply elist
  simp only [applicationPresentation,buildPresentation,automatonOfRaw]
  simp only [List.map_append,List.map_replicate,List.map_cons,List.map_nil]
  fun_prop
lemma record_primrec (f1 f2 f3 f4 f5 f6 f7 : α → ℕ)
    (h1 : Primrec f1) (h2 : Primrec f2) (h3 : Primrec f3) (h4 : Primrec f4)
    (h5 : Primrec f5) (h6 : Primrec f6) (h7 : Primrec f7) :
    Primrec (fun a => recordCode (f1 a) (f2 a) (f3 a) (f4 a) (f5 a) (f6 a) (f7 a)) := by
  unfold recordCode C N
  fun_prop
lemma application_code_primrec : Primrec (fun r : RawAutomaton =>
    Encodable.encode (applicationPresentation (automatonOfRaw r))) := by
  have htypes := types_code_primrec
  have hc : Primrec (fun r : RawAutomaton => Encodable.encode
      (applicationPresentation (automatonOfRaw r)).central) :=
    central_code_primrec.of_eq (fun r => congrArg Encodable.encode (centralNat_eq r))
  have hr : Primrec (fun r : RawAutomaton => (applicationPresentation (automatonOfRaw r)).root) := by
    simp only [applicationPresentation,buildPresentation,automatonOfRaw]
    exact Primrec.const _
  have ht : Primrec (fun r : RawAutomaton => Encodable.encode
      (applicationPresentation (automatonOfRaw r)).transported) := by
    simp only [applicationPresentation,buildPresentation,automatonOfRaw]
    exact Primrec.const _
  have he : Primrec (fun r : RawAutomaton => Encodable.encode
      (applicationPresentation (automatonOfRaw r)).endpoints) := by
    simp only [applicationPresentation,buildPresentation,automatonOfRaw]
    exact Primrec.const _
  have hz : Primrec (fun r : RawAutomaton => Encodable.encode
      (applicationPresentation (automatonOfRaw r)).zeros) := by
    simp only [applicationPresentation,buildPresentation,automatonOfRaw]
    exact Primrec.const _
  have hl : Primrec (fun r : RawAutomaton => Encodable.encode
      (applicationPresentation (automatonOfRaw r)).linear) := by
    simp only [applicationPresentation,buildPresentation,automatonOfRaw]
    exact Primrec.const _
  exact (record_primrec _ _ _ _ _ _ _ htypes hr ht hc he hz hl).of_eq
    (fun r => (record_code (applicationPresentation (automatonOfRaw r))).symm)
#print axioms application_code_primrec
end Sigma2.PresentationCoding
