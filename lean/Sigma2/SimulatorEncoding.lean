import Sigma2.ReductionInterface

noncomputable section
set_option maxHeartbeats 200000
namespace Sigma2.SimulatorEncoding
open Sigma2.Tree Sigma2.Reduction

def leftCode {n : ℕ} (l : Option (Fin n)) : ℕ :=
  (l.map (fun x => x.val+1)).getD 0

def bitCode (b : Bool) : ℕ := if b then 1 else 0

def localIndex {n : ℕ} (l : Option (Fin n)) (c d : Fin n) (b : Bool) : ℕ :=
  ((leftCode l*n+c.val)*n+d.val)*2+bitCode b

lemma pack_div (a d b : ℕ) (hd : 0 < d) (hb : b < d) :
    (a*d+b)/d = a := by
  rw [Nat.mul_comm a d, Nat.mul_add_div hd, Nat.div_eq_of_lt hb, Nat.add_zero]

lemma pack_mod (a d b : ℕ) (hb : b < d) : (a*d+b)%d = b := by
  rw [Nat.mul_comm a d, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]

lemma pack_lt {a A d b : ℕ} (ha : a < A) (hb : b < d) : a*d+b < A*d := by
  calc
    _ < a*d+d := Nat.add_lt_add_left hb _
    _ = (a+1)*d := by ring
    _ ≤ A*d := Nat.mul_le_mul_right d (by omega)

lemma leftCode_lt {n : ℕ} (l : Option (Fin n)) : leftCode l < n+1 := by
  cases l with
  | none => simp [leftCode]
  | some x => simp [leftCode]

lemma bitCode_lt (b : Bool) : bitCode b < 2 := by cases b <;> decide

lemma localIndex_lt {n : ℕ} (l : Option (Fin n)) (c d : Fin n) (b : Bool) :
    localIndex l c d b < ((n+1)*n*n)*2 :=
  pack_lt (pack_lt (pack_lt (leftCode_lt l) c.isLt) d.isLt) (bitCode_lt b)

/-- Decode mixed-radix local coordinates; index zero for the left neighbor means
that the cell is at the half-line boundary. -/
def localEntry (M : Automaton) (k : ℕ) : ℕ :=
  let n := M.extraSymbols+3
  let a := k/2/n/n
  (M.update
    (if a=0 then none else some ⟨(a-1)%n, Nat.mod_lt _ (by omega)⟩)
    ⟨(k/2/n)%n, Nat.mod_lt _ (by omega)⟩
    ⟨(k/2)%n, Nat.mod_lt _ (by omega)⟩
    (decide (k%2=1))).val

lemma localEntry_index (M : Automaton) (l : Option (Symbol M))
    (c d : Symbol M) (b : Bool) :
    localEntry M (localIndex l c d b) = (M.update l c d b).val := by
  let n := M.extraSymbols+3
  have hn : 0 < n := by dsimp [n]; omega
  have hbit : decide (bitCode b=1)=b := by cases b <;> decide
  have hdiv1 : localIndex l c d b/2=(leftCode l*n+c.val)*n+d.val :=
    pack_div _ _ _ (by omega) (bitCode_lt b)
  have hdiv2 : localIndex l c d b/2/n=leftCode l*n+c.val := by
    rw [hdiv1]
    exact pack_div _ _ _ hn d.isLt
  have hdiv3 : localIndex l c d b/2/n/n=leftCode l := by
    rw [hdiv2]
    exact pack_div _ _ _ hn c.isLt
  have hright : (localIndex l c d b/2)%n=d.val := by
    rw [hdiv1]
    exact pack_mod _ _ _ d.isLt
  have hcenter : (localIndex l c d b/2/n)%n=c.val := by
    rw [hdiv2]
    exact pack_mod _ _ _ c.isLt
  have hpulse : decide (localIndex l c d b%2=1)=b := by
    rw [show localIndex l c d b%2=bitCode b from pack_mod _ _ _ (bitCode_lt b)]
    exact hbit
  unfold localEntry
  change (M.update (if localIndex l c d b/2/n/n=0 then none else
    some ⟨(localIndex l c d b/2/n/n-1)%n, _⟩)
    ⟨(localIndex l c d b/2/n)%n, _⟩ ⟨(localIndex l c d b/2)%n, _⟩
    (decide (localIndex l c d b%2=1))).val = _
  simp only [hdiv3, hcenter, hright, hpulse]
  have hl : (if leftCode l=0 then none else
      some (⟨(leftCode l-1)%n, Nat.mod_lt _ hn⟩ : Fin n)) = l := by
    cases l with
    | none => simp [leftCode]
    | some x =>
        simp [leftCode]
        exact Fin.ext (Nat.mod_eq_of_lt x.isLt)
  rw [hl]

/-- An actual finite raw transition table in the existing decoder's format. -/
def rawOfAutomaton (M : Automaton) : RawAutomaton :=
  (M.extraSymbols, List.ofFn (fun k : Fin (((M.extraSymbols+4)*
    (M.extraSymbols+3)*(M.extraSymbols+3))*2) => localEntry M k.val))

def code (M : Automaton) : ℕ := Encodable.encode (rawOfAutomaton M)

lemma raw_lookup (M : Automaton) (l : Option (Symbol M)) (c d : Symbol M) (b : Bool) :
    ((rawOfAutomaton M).2[localIndex l c d b]?).getD 1 = (M.update l c d b).val := by
  unfold rawOfAutomaton
  simp only [List.getElem?_ofFn]
  rw [dite_eq_left (localIndex_lt l c d b)]
  exact localEntry_index M l c d b

/-- The existing raw decoder recovers every quiescent transition table exactly. -/
theorem raw_roundtrip (M : Automaton) : automatonOfRaw (rawOfAutomaton M) = M := by
  have he : (automatonOfRaw (rawOfAutomaton M)).update = M.update := by
    change (fun (l : Option (Symbol M)) (c d : Symbol M) (b : Bool) =>
      if l=some 1 ∧ c=1 ∧ d=1 then 1 else
        (⟨(((rawOfAutomaton M).2[localIndex l c d b]?).getD 1)%(M.extraSymbols+3),
          Nat.mod_lt _ (by omega)⟩ : Fin (M.extraSymbols+3))) = M.update
    funext l c d b
    change (if l=some 1 ∧ c=1 ∧ d=1 then 1 else
      (⟨(((rawOfAutomaton M).2[localIndex l c d b]?).getD 1)%(M.extraSymbols+3), _⟩ :
        Fin (M.extraSymbols+3))) = M.update l c d b
    split_ifs with hb
    · rcases hb with ⟨rfl, rfl, rfl⟩
      exact (M.blank_quiescence b).symm
    · apply Fin.ext
      change (((rawOfAutomaton M).2[localIndex l c d b]?).getD 1)%(M.extraSymbols+3) = _
      rw [raw_lookup M l c d b]
      exact Nat.mod_eq_of_lt (M.update l c d b).isLt
  cases M with
  | mk n upd hb =>
    change Automaton.mk n _ _ = Automaton.mk n upd hb
    congr 1

/-- A natural-number code in precisely Reduction.decodeAutomaton's format. -/
theorem decode_code (M : Automaton) : decodeAutomaton (code M) = M := by
  unfold code decodeAutomaton
  rw [Encodable.encodek]
  exact raw_roundtrip M

#print axioms raw_roundtrip
#print axioms decode_code
#print axioms localIndex_lt
#print axioms localEntry_index
end Sigma2.SimulatorEncoding




