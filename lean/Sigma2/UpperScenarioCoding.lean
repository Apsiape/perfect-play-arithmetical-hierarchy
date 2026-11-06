import Sigma2.UpperEffective

/-! Effective decoding of the frozen derived Scenario encoding.
The derived encoder uses a fixed-depth tree of natural-number pairs. -/
set_option maxHeartbeats 100000
namespace Sigma2.UpperScenarioCoding
open Primrec

abbrev Fields := ℕ × ℕ × ℕ × ℕ

def fields (s : Scenario) : Fields := (s.questionsA,s.questionsB,s.answersA,s.answersB)
def ofFields (p : Fields) : Scenario := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2⟩
def node (a b : ℕ) : ℕ := Nat.pair (Nat.pair 0 a + 1) b
def code (p : Fields) : ℕ := node 0 (node p.1 (node p.2.1 (node p.2.2.1 (node p.2.2.2 0))))
def tail (c : ℕ) : ℕ := c.unpair.2
def head (c : ℕ) : ℕ := (c.unpair.1-1).unpair.2
def candidate (c : ℕ) : Fields :=
  (head (tail c),head (tail (tail c)),head (tail (tail (tail c))),head (tail (tail (tail (tail c)))))
def parse (c : ℕ) : Option Fields := if code (candidate c) = c then some (candidate c) else none

@[simp] theorem fields_ofFields (p : Fields) : fields (ofFields p) = p := rfl
@[simp] theorem ofFields_fields (s : Scenario) : ofFields (fields s) = s := by cases s; rfl
@[simp] theorem head_node (a b : ℕ) : head (node a b) = a := by simp [head,node]
@[simp] theorem tail_node (a b : ℕ) : tail (node a b) = b := by simp [tail,node]
@[simp] theorem candidate_code (p : Fields) : candidate (code p) = p := by simp [candidate,code]
@[simp] theorem parse_code (p : Fields) : parse (code p) = some p := by simp [parse]

theorem code_eq_encode (s : Scenario) : code (fields s) = Encodable.encode s := by
  cases s
  rfl

elab "upperPrivate" s:str : term => do
  let env ← Lean.getEnv
  let some (name,_) := env.constants.toList.find? (fun (name,_) => name.toString == s.getString)
    | throwError "Missing frozen encoding helper {s.getString}"
  return Lean.mkConst name

private abbrev Tree := upperPrivate "_private.Mathlib.Tactic.DeriveEncodable.0.Mathlib.Deriving.Encodable.S"
private abbrev treeDecode := upperPrivate "_private.Mathlib.Tactic.DeriveEncodable.0.Mathlib.Deriving.Encodable.S.decode"
private abbrev treeEncode := upperPrivate "_private.Mathlib.Tactic.DeriveEncodable.0.Mathlib.Deriving.Encodable.S.encode"
@[match_pattern] private abbrev tnat := upperPrivate "_private.Mathlib.Tactic.DeriveEncodable.0.Mathlib.Deriving.Encodable.S.nat"
@[match_pattern] private abbrev tcons := upperPrivate "_private.Mathlib.Tactic.DeriveEncodable.0.Mathlib.Deriving.Encodable.S.cons"
private def fromTree : Tree → Option Scenario
  | tcons (tnat 0) (tcons (tnat a) (tcons (tnat b) (tcons (tnat c) (tcons (tnat d) (tnat 0))))) => some ⟨a,b,c,d⟩
  | _ => none

private theorem decode_tree (c : ℕ) :
    Encodable.decode (α := Scenario) c = fromTree (treeDecode c) := by rfl

theorem decode_canonical (c : ℕ) (s : Scenario) (h : Encodable.decode c = some s) :
    Encodable.encode s = c := by
  rw [decode_tree] at h
  have he : treeEncode (treeDecode c) = Encodable.encode s := by
    generalize treeDecode c = t at h ⊢
    unfold fromTree at h
    split at h
    · cases Option.some.inj h
      rfl
    · contradiction
  exact he.symm.trans ((upperPrivate "_private.Mathlib.Tactic.DeriveEncodable.0.Mathlib.Deriving.Encodable.S_equiv").right_inv c)

theorem decode_eq (c : ℕ) :
    Encodable.decode (α := Scenario) c = (parse c).map ofFields := by
  cases h : Encodable.decode (α := Scenario) c with
  | some s =>
      have hc := decode_canonical c s h
      rw [← hc,← code_eq_encode,parse_code]
      simp
  | none =>
      cases hp : parse c with
      | none => rfl
      | some p =>
          have hc : code p = c := by
            unfold parse at hp
            split_ifs at hp with he
            · have hh := Option.some.inj hp
              exact hh ▸ he
          have hd : Encodable.decode (α := Scenario) c = some (ofFields p) := by
            rw [← hc,show code p = Encodable.encode (ofFields p) from code_eq_encode (ofFields p)]
            exact Encodable.encodek _
          rw [h] at hd
          cases hd

attribute [fun_prop] Primrec.unpair Primrec.pred
@[fun_prop] theorem pr_nat_pair : Primrec (fun p : ℕ × ℕ => Nat.pair p.1 p.2) := Primrec₂.natPair
@[fun_prop] theorem pr_nat_sub : Primrec (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub
@[fun_prop] theorem node_primrec : Primrec (fun p : ℕ × ℕ => node p.1 p.2) := by unfold node; fun_prop
@[fun_prop] theorem code_primrec : Primrec code := by unfold code; fun_prop
@[fun_prop] theorem tail_primrec : Primrec tail := by unfold tail; fun_prop
@[fun_prop] theorem head_primrec : Primrec head := by unfold head; fun_prop
@[fun_prop] theorem candidate_primrec : Primrec candidate := by unfold candidate; fun_prop

theorem parse_primrec : Primrec parse :=
  Primrec.ite (Primrec.eq.comp (code_primrec.comp candidate_primrec) .id)
    (Primrec.option_some.comp candidate_primrec) (Primrec.const none)

theorem decode_encode_eq (c : ℕ) :
    Encodable.encode (Encodable.decode (α := Scenario) c) =
      if code (candidate c) = c then code (candidate c) + 1 else 0 := by
  rw [decode_eq]
  unfold parse
  split_ifs
  · change Encodable.encode (ofFields (candidate c)) + 1 = code (candidate c) + 1
    rw [← code_eq_encode,fields_ofFields]
  · rfl

theorem scenario_prim : Nat.Primrec (fun c : ℕ => Encodable.encode (Encodable.decode (α := Scenario) c)) := by
  have h : Primrec (fun c : ℕ => if code (candidate c) = c then code (candidate c)+1 else 0) :=
    Primrec.ite (Primrec.eq.comp (code_primrec.comp candidate_primrec) Primrec.id)
      (Primrec.succ.comp (code_primrec.comp candidate_primrec)) (Primrec.const 0)
  exact (Primrec.nat_iff.mp h).of_eq (fun c => (decode_encode_eq c).symm)
instance : Primcodable Scenario where
  toEncodable := Sigma2.instEncodableScenario
  prim := scenario_prim

end Sigma2.UpperScenarioCoding