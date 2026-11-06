import Sigma2.ReductionInterface
import Mathlib.Computability.Primrec.List

set_option maxHeartbeats 200000
namespace Sigma2.SimulatorChecks
open Sigma2.Reduction

/-- Trial division is primitive recursive; this is a computability certificate,
rather than an appeal to the mere existence of a decidability instance. -/
theorem prime_primrec : PrimrecPred Nat.Prime := by
  have hd : PrimrecRel (fun m q : ℕ => m ∣ q) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
      (fun x => (Nat.dvd_iff_mod_eq_zero).symm)
  have hr : PrimrecRel (fun m q : ℕ => ¬m ∣ q ∨ m=1) :=
    hd.not.or (Primrec.eq.comp Primrec.fst (Primrec.const 1))
  have ha : PrimrecPred (fun q : ℕ => ∀ m<q, ¬m ∣ q ∨ m=1) :=
    hr.forall_lt.comp Primrec.id Primrec.id
  exact ((Primrec.nat_le.comp (Primrec.const 2) Primrec.id).and ha).of_eq
    (fun q => by simp only [Nat.prime_def_lt, imp_iff_not_or, id_eq])

/-- The zero-based rank of a prime in the paper's exact PrimeRank convention. -/
def primeCount (q : ℕ) : ℕ := ((List.range q).filter (fun m => decide (Nat.Prime m))).length

theorem primeCount_primrec : Primrec primeCount :=
  Primrec.list_length.comp ((Primrec.listFilter prime_primrec).comp Primrec.list_range)

theorem primeCount_eq (q : ℕ) :
    primeCount q = ((Finset.range q).filter Nat.Prime).card := by
  rfl

theorem primeRank_iff (n q : ℕ) : PrimeRank n q ↔ Nat.Prime q ∧ primeCount q=n := by
  rw [PrimeRank, primeCount_eq]

theorem primeRank_unique {m n q : ℕ} (hm : PrimeRank m q) (hn : PrimeRank n q) : m=n := by
  exact hm.2.symm.trans hn.2

/-- A total prime-rank decoder, with rejection for 0, 1, and composites. -/
def decodePrimeRank (q : ℕ) : Option ℕ :=
  if Nat.Prime q then some (primeCount q) else none

theorem decodePrimeRank_primrec : Primrec decodePrimeRank :=
  Primrec.ite prime_primrec (Primrec.option_some.comp primeCount_primrec) (Primrec.const none)

theorem decodePrimeRank_some (q n : ℕ) : decodePrimeRank q=some n ↔ PrimeRank n q := by
  rw [primeRank_iff]
  by_cases hp : Nat.Prime q <;> simp [decodePrimeRank, hp]

/-- Sequential checking at the abstract machine level: stage t records all
checks 0 through t-1. The CA implementation must still simulate these stages. -/
def checkPrefix (R : ℕ × ℕ × ℕ → Bool) (e n : ℕ) : ℕ → Bool
  | 0 => true
  | t+1 => checkPrefix R e n t && R (e,n,t)

theorem checkPrefix_spec (R : ℕ × ℕ × ℕ → Bool) (e n t : ℕ) :
    checkPrefix R e n t=true ↔ ∀ s<t, R (e,n,s)=true := by
  induction t with
  | zero => simp [checkPrefix]
  | succ t ih => simp only [checkPrefix, Bool.and_eq_true, ih, Nat.lt_succ_iff_lt_or_eq]; aesop

theorem checkPrefix_all (R : ℕ × ℕ × ℕ → Bool) (e n : ℕ) :
    (∀ t, checkPrefix R e n t=true) ↔ ∀ t, R (e,n,t)=true := by
  constructor
  · intro h t
    exact (checkPrefix_spec R e n (t+1)).mp (h (t+1)) t (by omega)
  · intro h t
    exact (checkPrefix_spec R e n t).mpr (fun s _ => h s)

theorem checkPrefix_computable (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    Computable (fun x : ℕ × ℕ × ℕ => checkPrefix R x.1 x.2.1 x.2.2) := by
  have hstep : Computable (fun z : (ℕ × ℕ × ℕ) × (ℕ × Bool) =>
      z.2.2 && R (z.1.1,z.1.2.1,z.2.1)) :=
    Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (hR.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          (Computable.fst.comp Computable.snd))))
  have hh := Computable.nat_rec (Computable.snd.comp Computable.snd)
    (Computable.const true) hstep.to₂
  apply hh.of_eq
  intro x
  induction x.2.2 with
  | zero => rfl
  | succ t ih => change (_ && R (x.1,x.2.1,t)) = _; rw [ih]; rfl

/-- The sequential verifier after pulse-period extraction. This is an abstract
algorithm, not the missing finite-state CA simulation of the algorithm. -/
def verifyStage (R : ℕ × ℕ × ℕ → Bool) (e q t : ℕ) : Bool :=
  if Nat.Prime q then checkPrefix R e (primeCount q) t else false

theorem verifyStage_computable (R : ℕ × ℕ × ℕ → Bool) (hR : Computable R) :
    Computable (fun x : ℕ × ℕ × ℕ => verifyStage R x.1 x.2.1 x.2.2) := by
  simpa only [verifyStage, Bool.cond_decide] using
   Computable.cond (prime_primrec.comp (Primrec.fst.comp Primrec.snd)).decide.to_comp
    ((checkPrefix_computable R hR).comp
      (Computable.fst.pair ((primeCount_primrec.to_comp.comp
        (Computable.fst.comp Computable.snd)).pair (Computable.snd.comp Computable.snd))))
    (Computable.const false)

theorem verifyStage_all (R : ℕ × ℕ × ℕ → Bool) (e q : ℕ) :
    (∀ t, verifyStage R e q t=true) ↔ ∃ n, PrimeRank n q ∧ ∀ t, R (e,n,t)=true := by
  by_cases hp : Nat.Prime q
  · simp only [verifyStage, ite_eq_left hp]
    rw [checkPrefix_all]
    constructor
    · intro h
      exact ⟨primeCount q, (primeRank_iff _ _).mpr ⟨hp,rfl⟩,h⟩
    · rintro ⟨n, hn, h⟩
      have he := (primeRank_iff n q).mp hn
      simpa only [he.2] using h
  · simp [verifyStage, hp, PrimeRank]

#print axioms verifyStage_computable
#print axioms verifyStage_all
#print axioms checkPrefix_computable
#print axioms prime_primrec
#print axioms primeCount_primrec
#print axioms decodePrimeRank_primrec
#print axioms decodePrimeRank_some
#print axioms checkPrefix_all
end Sigma2.SimulatorChecks




