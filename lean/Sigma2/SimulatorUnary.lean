import Sigma2.SimulatorVerifier

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace Sigma2.SimulatorUnary
open Turing Sigma2.Reduction

def ones : ℕ → ℕ
  | 0 => 0
  | q+1 => 2 * ones q + 1

lemma ones_strictMono : StrictMono ones := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [ones]
  omega

theorem ones_injective : Function.Injective ones := ones_strictMono.injective

theorem ones_primrec : Primrec ones := by
  have h := Primrec.nat_rec₁ (0 : ℕ)
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)
      (Primrec.const 1)).to₂)
  apply h.of_eq
  intro q
  induction q with
  | zero => rfl
  | succ q ih => change 2 * _ + 1 = 2 * ones q + 1; rw [ih]

lemma trNum_bit1 (n : Num) :
    PartrecToTM2.trNum n.bit1 = PartrecToTM2.Γ'.bit1 :: PartrecToTM2.trNum n := by
  cases n <;> rfl

/-- A unary block of q cells is exactly Mathlib's binary encoding of ones q. -/
theorem trNat_ones (q : ℕ) :
    PartrecToTM2.trNat (ones q) = List.replicate q PartrecToTM2.Γ'.bit1 := by
  induction q with
  | zero => simp [ones]
  | succ q ih =>
    have hc : ((ones (q+1) : ℕ) : Num) = ((ones q : ℕ) : Num).bit1 := by
      simp only [ones, two_mul, Nat.cast_add, Nat.cast_one, Num.bit1_of_bit1]
    change PartrecToTM2.trNum _ = _
    rw [hc, trNum_bit1]
    change _ :: PartrecToTM2.trNat (ones q) = _
    rw [ih, List.replicate_succ]

def unones (n : ℕ) : Part ℕ :=
  Nat.rfind (fun q => Part.some (decide (ones q=n)))

theorem unones_partrec : Partrec unones := by
  have hp : Computable (fun v : ℕ × ℕ => decide (ones v.2=v.1)) :=
    (Primrec.eq.comp (ones_primrec.comp Primrec.snd) Primrec.fst).decide.to_comp
  exact Partrec.rfind hp.partrec.to₂

/-- The search is exact on every captured block; it cannot confuse periods. -/
theorem unones_ones (q : ℕ) : unones (ones q) = Part.some q := by
  apply Part.eq_some_iff.mpr
  apply Nat.mem_rfind.mpr
  constructor
  · simp
  · intro m hm
    have hn : ones m ≠ ones q := fun h => (by omega : m≠q) (ones_injective h)
    simp [hn]

/-- An actual list program converts the unary-block representation to [q]. -/
theorem decoder_code :
    ∃ d : ToPartrec.Code, ∀ q, d.eval [ones q] = Part.some [q] := by
  have hp : Partrec (fun v : List.Vector ℕ 1 => unones v.head) :=
    unones_partrec.comp Computable.vector_head
  obtain ⟨d, hd⟩ := ToPartrec.Code.exists_code (Nat.Partrec'.of_part hp)
  refine ⟨d, fun q => ?_⟩
  have h := hd (⟨[ones q], rfl⟩ : List.Vector ℕ 1)
  change d.eval [ones q] = (fun n => [n]) <$> unones (ones q) at h
  simpa only [Part.map_eq_map, unones_ones, Part.map_some] using h

def parameterCode : ℕ → ToPartrec.Code
  | 0 => .zero
  | e+1 => .comp .succ (parameterCode e)

lemma parameterCode_eval (e : ℕ) (v : List ℕ) :
    (parameterCode e).eval v = Part.some [e] := by
  induction e with
  | zero => simp [parameterCode]
  | succ e ih => simp [parameterCode, ih]

/-- The hardcoded parameter and decoded unary block have the exact [e,q]
stack input expected by the previously compiled verifier. -/
theorem loader_code : ∃ d : ToPartrec.Code, ∀ e q,
    (ToPartrec.Code.cons (parameterCode e) d).eval [ones q] = Part.some [e,q] := by
  obtain ⟨d, hd⟩ := decoder_code
  exact ⟨d, fun e q => by simp [parameterCode_eval, hd]⟩

/-- Checked composition with the existing sequential verifier. -/
theorem unary_code (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    ∃ c d : ToPartrec.Code, ∀ e q,
      ((ToPartrec.Code.comp c (.cons (parameterCode e) d)).eval [ones q]).Dom ↔
        ¬ ∃ n, PrimeRank n q ∧ ∀ t, R (e,n,t)=true := by
  obtain ⟨c, hc⟩ := SimulatorVerifier.exists_code R hR
  obtain ⟨d, hd⟩ := loader_code
  refine ⟨c, d, fun e q => ?_⟩
  have hcomp : (ToPartrec.Code.comp c (.cons (parameterCode e) d)).eval [ones q] =
      c.eval [e,q] := by
    change ((ToPartrec.Code.cons (parameterCode e) d).eval [ones q]).bind
      (fun w => c.eval w) = _
    rw [hd]
    exact Part.bind_some _ _
  rw [hcomp]
  have he := hc (⟨[e,q], rfl⟩ : List.Vector ℕ 2)
  rw [he]
  exact SimulatorVerifier.rejectSearch_dom R _

/-- The compiled unary-input verifier has a genuinely finite state space. -/
theorem finite_unary_verifier (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) (e : ℕ) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Inhabited Q)
      (M : TM0.Machine SimulatorMachine.TapeAlphabet Q), ∀ q,
        (TM0.eval M (SimulatorMachine.input [ones q])).Dom ↔
          ¬ ∃ n, PrimeRank n q ∧ ∀ t, R (e,n,t)=true := by
  classical
  obtain ⟨c, d, hcd⟩ := unary_code R hR
  let code := ToPartrec.Code.comp c (.cons (parameterCode e) d)
  letI : Inhabited PartrecToTM2.Λ' := ⟨PartrecToTM2.trNormal code PartrecToTM2.Cont'.halt⟩
  obtain ⟨S, hs⟩ := SimulatorMachine.finite_support code
  let M := TM1to0.tr SimulatorMachine.machine1
  letI : Fact ((default : SimulatorMachine.Labels0) ∈ S) := ⟨hs.1⟩
  refine ⟨{q // q ∈ S}, inferInstance, inferInstance, SimulatorFinite.machine M S hs, ?_⟩
  intro q
  rw [SimulatorFinite.eval_exact M S hs]
  change (SimulatorMachine.runCode code [ones q]).Dom ↔ _
  rw [SimulatorMachine.runCode_dom]
  exact hcd e q

#print axioms trNat_ones
#print axioms unones_ones
#print axioms loader_code
#print axioms unary_code
#print axioms finite_unary_verifier
end Sigma2.SimulatorUnary
