import Sigma2.CompilerEffectiveBool
import Mathlib.Data.Nat.Bitwise
noncomputable section
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false
namespace Sigma2.CompilerEffectiveCoding
open CompilerEffective
attribute [local irreducible] Nat.pair Nat.lt Encodable.encodeList Nat.log Nat.xor Nat.bit
attribute [local fun_prop] Computable Computable₂ Computable.id Computable.const
  Computable.fst Computable.snd Computable.comp Computable.pair Computable.cond Computable.unpair Computable.option_some
variable {α : Type} [Primcodable α]

/-- The least exponent whose following power exceeds the input is exactly log_4. -/
theorem log4_computable : Computable (Nat.log 4) := by
  have hpow : Primrec (fun z : ℕ × ℕ => 4^(z.2+1)) :=
    (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 4) (Primrec.succ.comp Primrec.snd)
  have hp : ComputablePred (fun z : ℕ × ℕ => z.1<4^(z.2+1)) :=
    (Primrec.nat_lt.comp Primrec.fst hpow).computablePred
  have hx : ∀ n : ℕ, ∃ k : ℕ, n<4^(k+1) := fun n => ⟨Nat.log 4 n,Nat.lt_pow_succ_log_self (by decide) n⟩
  apply (Computable.find hp hx).of_eq
  intro n
  apply le_antisymm
  · exact Nat.find_min' (hx n) (Nat.lt_pow_succ_log_self (by decide) n)
  · by_cases hn : n=0
    · simp [hn]
    · have hh := (Nat.log_lt_iff_lt_pow (by decide : 1<4) hn).mpr (Nat.find_spec (hx n))
      omega
@[fun_prop] theorem clog4 (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => Nat.log 4 (f a)) := log4_computable.comp hf

@[fun_prop] theorem cbodd (f : α → ℕ) (hf : Computable f) :
    Computable (fun a => Nat.bodd (f a)) := Primrec.nat_bodd.to_comp.comp hf
@[fun_prop] theorem cboolNe (f g : α → Bool) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => bne (f a) (g a)) := (Primrec.dom_bool₂ (fun a b : Bool => bne a b)).to_comp.comp hf hg
@[fun_prop] theorem cnatPair (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => Nat.pair (f a) (g a)) := Primrec₂.natPair.to_comp.comp hf hg

theorem natBit_computable : Computable (fun z : Bool × ℕ => Nat.bit z.1 z.2) := by
  unfold Nat.bit
  fun_prop
@[fun_prop] theorem cnatBit (b : α → Bool) (n : α → ℕ) (hb : Computable b) (hn : Computable n) :
    Computable (fun a => Nat.bit (b a) (n a)) := natBit_computable.comp (hb.pair hn)

theorem testBit_computable : Computable (fun z : ℕ × ℕ => Nat.testBit z.1 z.2) := by
  have hc : Computable (fun z : ℕ × ℕ => decide ((z.1/2^z.2)%2=1)) := by fun_prop
  apply hc.of_eq
  intro z
  rcases Nat.mod_two_eq_zero_or_one (z.1/2^z.2) with h | h <;>
    simp [Nat.testBit,Nat.shiftRight_eq_div_pow,Nat.one_and_eq_mod_two,h]
@[fun_prop] theorem ctestBit (n k : α → ℕ) (hn : Computable n) (hk : Computable k) :
    Computable (fun a => Nat.testBit (n a) (k a)) := testBit_computable.comp (hn.pair hk)

def xorNorm (n : ℕ) : ℕ := Nat.xor (Nat.unpair n).1 (Nat.unpair n).2

def xorStep (n : ℕ) (previous : ℕ → ℕ) : ℕ :=
  let p := Nat.unpair n
  if p.1=0 then p.2 else if p.2=0 then p.1 else
    Nat.bit (bne (Nat.bodd p.1) (Nat.bodd p.2)) (previous (Nat.pair (p.1/2) (p.2/2)))

theorem xorStep_agrees (n : ℕ) : xorStep n xorNorm=xorNorm n := by
  obtain ⟨⟨a,b⟩,rfl⟩ := Nat.pairEquiv.surjective n
  change xorStep (Nat.pair a b) xorNorm=xorNorm (Nat.pair a b)
  simp only [xorStep,xorNorm,Nat.unpair_pair]
  by_cases ha : a=0
  · subst a; simp [Nat.xor]
  · by_cases hb : b=0
    · subst b; simp [Nat.xor,ha]
    · rw [if_neg ha,if_neg hb]
      simpa only [Nat.xor,Nat.unpair_pair] using (Nat.bitwise_of_ne_zero (f := fun a b : Bool => bne a b) ha hb).symm

theorem xorStep_congr (n : ℕ) (f g : ℕ → ℕ) (h : ∀ k, k<n → f k=g k) :
    xorStep n f=xorStep n g := by
  obtain ⟨⟨a,b⟩,rfl⟩ := Nat.pairEquiv.surjective n
  change xorStep (Nat.pair a b) f=xorStep (Nat.pair a b) g
  simp only [xorStep,Nat.unpair_pair]
  by_cases ha : a=0
  · simp [ha]
  · by_cases hb : b=0
    · simp [hb]
    · have hh : Nat.pair (a/2) (b/2)<Nat.pair a b :=
        lt_trans (Nat.pair_lt_pair_left (b/2) (Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by decide)))
          (Nat.pair_lt_pair_right a (Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)))
      simp only [if_neg ha,if_neg hb,h _ hh]

def xorTable (l : List ℕ) : Option ℕ := some (xorStep l.length (fun k => l[k]?.getD 0))
theorem xorTable_computable : Computable xorTable := by unfold xorTable xorStep; fun_prop

theorem xorNorm_computable : Computable xorNorm := by
  have hg : Computable (fun z : Unit × List ℕ => xorTable z.2) := xorTable_computable.comp Computable.snd
  have hs := Computable.nat_strong_rec (fun (_ : Unit) n => xorNorm n) hg.to₂ (by
    intro _ n
    simp only [xorTable,List.length_map,List.length_range]
    apply congrArg some
    rw [xorStep_congr n _ xorNorm (by intro k hk; simp [hk])]
    exact xorStep_agrees n)
  exact hs.comp (Computable.const ()) Computable.id

theorem natXor_computable : Computable (fun z : ℕ × ℕ => Nat.xor z.1 z.2) :=
  (xorNorm_computable.comp Primrec₂.natPair.to_comp).of_eq (fun z => by simp [xorNorm])
@[fun_prop] theorem cnatXor (f g : α → ℕ) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => Nat.xor (f a) (g a)) := natXor_computable.comp (hf.pair hg)

#print axioms log4_computable
#print axioms testBit_computable
#print axioms natXor_computable
end Sigma2.CompilerEffectiveCoding