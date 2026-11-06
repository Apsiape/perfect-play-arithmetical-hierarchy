import Sigma2.UpperEntropySchedule
import Sigma2.UpperEntropyEffective

namespace Sigma2.UpperEntropyQuantifiers
open UpperEntropySchedule

/-- Universal indices pair the loss stage and polynomial precision. -/
def decisionInput (coeff : ℕ × ℕ → List (ℤ × ℕ)) (p : ℕ × ℕ × ℕ) :
    UpperEntropyEffective.CodeInput :=
  let t := p.2.2.unpair.1
  let k := p.2.2.unpair.2
  let n := stageIndex p.2.1 t
  (p.1,p.2.1,n,k,1/(t+1:ℚ),coeff (n,k+1))

theorem decisionInput_computable (coeff : ℕ × ℕ → List (ℤ × ℕ)) (hc : Computable coeff) :
    Computable (decisionInput coeff) := by
  have ht : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  have hk : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd))
  have hB : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn := stageIndex_primrec.comp (hB.pair ht)
  have hcoeff := hc.comp (hn.to_comp.pair (Primrec.succ.comp hk).to_comp)
  have hη : Computable (fun p : ℕ × ℕ × ℕ => (1:ℚ)/(p.2.2.unpair.1+1)) :=
    UpperCoding.rat_fraction.comp ((Computable.const (1:ℤ)).pair ht.to_comp)
  exact Computable.fst.pair (hB.to_comp.pair (hn.to_comp.pair
    (hk.to_comp.pair (hη.pair hcoeff))))

theorem forall_unpair (P : ℕ → ℕ → Prop) :
    (∀ i : ℕ,P i.unpair.1 i.unpair.2) ↔ ∀ t k,P t k := by
  constructor
  · intro h t k
    simpa only [Nat.unpair_pair] using h (Nat.pair t k)
  · intro h i
    exact h _ _

/-- Every occurrence of a valid code denotes the same game. -/
theorem gameProperty_forall {ι : Type} (i₀ : ι) (P : ι → Game → Prop) (c : ℕ) :
    GameProperty (fun G => ∀ i,P i G) c ↔ ∀ i,GameProperty (P i) c := by
  constructor
  · rintro ⟨G,hG,h⟩ i
    exact ⟨G,hG,h i⟩
  · intro h
    obtain ⟨G,hG,_⟩ := h i₀
    refine ⟨G,hG,fun i => ?_⟩
    obtain ⟨G',hG',hi⟩ := h i
    have hh : G'=G := Option.some.inj (hG'.symm.trans hG)
    simpa only [hh] using hi

end Sigma2.UpperEntropyQuantifiers
