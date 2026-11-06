import Sigma2.SimulatorStandard

noncomputable section
set_option maxHeartbeats 400000
namespace Sigma2.SimulatorUniform
open Sigma2.Reduction Sigma2.Tree

/-- Explicit bounded enumeration, with the parameter retained at each step. -/
def rows (entry : ℕ → ℕ → ℕ) (e : ℕ) : ℕ → List ℕ
  | 0 => []
  | n+1 => rows entry e n ++ [entry e n]

lemma rows_eq (entry : ℕ → ℕ → ℕ) (e n : ℕ) :
    rows entry e n = (List.range n).map (entry e) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rows, ih, List.range_succ]

theorem rows_computable (entry : ℕ → ℕ → ℕ)
    (hentry : Computable₂ entry) : Computable₂ (rows entry) := by
  have hs : Computable (fun z : (ℕ × ℕ) × (ℕ × List ℕ) =>
      z.2.2 ++ [entry z.1.1 z.2.1]) :=
    Primrec.list_concat.to_comp.comp (Computable.snd.comp Computable.snd)
      (hentry.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
  have hh := Computable.nat_rec Computable.snd (Computable.const ([] : List ℕ)) hs.to₂
  apply hh.of_eq
  intro z
  induction z.2 with
  | zero => rfl
  | succ n ih => change _ ++ [entry z.1 n] = _; rw [ih]; rfl

/-- The exact mixed-radix support size already used by rawOfAutomaton. -/
def tableSize (extra : ℕ) : ℕ := (extra+4)*(extra+3)*(extra+3)*2

theorem tableSize_primrec : Primrec tableSize :=
  (Primrec.nat_mul.comp
    (Primrec.nat_mul.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_add.comp Primrec.id (Primrec.const 4))
        (Primrec.nat_add.comp Primrec.id (Primrec.const 3)))
      (Primrec.nat_add.comp Primrec.id (Primrec.const 3)))
    (Primrec.const 2))

/-- A transition-table compiler using an explicit computable alphabet-size
function and a computable local-entry kernel. No arbitrary finite enumeration
is selected by this definition. -/
def rawFamily (extra : ℕ → ℕ) (entry : ℕ → ℕ → ℕ) (e : ℕ) : RawAutomaton :=
  (extra e, rows entry e (tableSize (extra e)))

def codeFamily (extra : ℕ → ℕ) (entry : ℕ → ℕ → ℕ) (e : ℕ) : ℕ :=
  Encodable.encode (rawFamily extra entry e)

theorem codeFamily_computable (extra : ℕ → ℕ) (entry : ℕ → ℕ → ℕ)
    (hextra : Computable extra) (hentry : Computable₂ entry) :
    Computable (codeFamily extra entry) := by
  have hr : Computable (rawFamily extra entry) :=
    hextra.pair ((rows_computable entry hentry).comp Computable.id
      (tableSize_primrec.to_comp.comp hextra))
  exact Computable.encode.comp hr

lemma rows_ofFn (f : ℕ → ℕ) (n : ℕ) :
    rows (fun _ => f) 0 n = List.ofFn (fun k : Fin n => f k.val) := by
  rw [rows_eq]
  apply List.ext_getElem <;> simp

/-- Exact agreement with the unchanged raw transition table serializer. -/
theorem rawFamily_eq (A : ℕ → Automaton) :
    rawFamily (fun e => (A e).extraSymbols)
      (fun e k => SimulatorEncoding.localEntry (A e) k) =
      fun e => SimulatorEncoding.rawOfAutomaton (A e) := by
  funext e
  apply Prod.ext
  · rfl
  · change rows _ e (tableSize (A e).extraSymbols) =
      List.ofFn (fun k : Fin (tableSize (A e).extraSymbols) =>
        SimulatorEncoding.localEntry (A e) k.val)
    simpa only [rows_eq] using
      rows_ofFn (fun k => SimulatorEncoding.localEntry (A e) k) (tableSize (A e).extraSymbols)

/-- Uniform finite support enumeration and serialization are checked once the
numeric local-entry kernel and alphabet-size family have computability proofs.
This criterion does not assert those premises for a chosen machine family. -/
theorem encoded_family_computable (A : ℕ → Automaton)
    (hsize : Computable (fun e => (A e).extraSymbols))
    (hentry : Computable₂ (fun e k => SimulatorEncoding.localEntry (A e) k)) :
    Computable (fun e => SimulatorEncoding.code (A e)) := by
  have h := codeFamily_computable (fun e => (A e).extraSymbols)
    (fun e k => SimulatorEncoding.localEntry (A e) k) hsize hentry
  apply h.of_eq
  intro e
  change Encodable.encode (rawFamily _ _ e) = _
  rw [rawFamily_eq]
  rfl

/-- An exact sufficient uniformity interface for the remaining original target. -/
theorem effective_of_uniform (R : ℕ × ℕ × ℕ → Bool) (A : ℕ → Automaton)
    (hcorrect : ∀ e, ProgramCorrect R e (A e))
    (hsize : Computable (fun e => (A e).extraSymbols))
    (hentry : Computable₂ (fun e k => SimulatorEncoding.localEntry (A e) k)) :
    ∃ f : ℕ → ℕ, Computable f ∧ ∀ e, ProgramCorrect R e (decodeAutomaton (f e)) := by
  refine ⟨fun e => SimulatorEncoding.code (A e), encoded_family_computable A hsize hentry, ?_⟩
  intro e
  rw [SimulatorEncoding.decode_code]
  exact hcorrect e

#print axioms codeFamily_computable
#print axioms rawFamily_eq
#print axioms encoded_family_computable
#print axioms effective_of_uniform
end Sigma2.SimulatorUniform
