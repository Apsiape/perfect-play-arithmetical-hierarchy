import Sigma2.FiniteSpectral

noncomputable section
open scoped BigOperators
namespace Sigma2.FiniteJoint
open Compiler CoarseCells FiniteSpectral Preliminaries PureSupport

/-- Ordered intersection of the actual sharp binary marginals. -/
def intersection {κ : Type} (P : Op) (C : κ → Op) : List κ → Op
  | [] => P
  | k::ks => C k * intersection P C ks

theorem intersection_action {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Op) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (f : κ → ι → Bool) (v : κ → Bool)
    (hp : ∀ k,Projection (coarse B (f k) (v k))) (ks : List κ) (a : ι) :
    intersection P (fun k => coarse B (f k) (v k)) ks * B a=
      if ∀ k ∈ ks,f k a=v k then B a else 0 := by
  induction ks with
  | nil =>
    simp only [intersection,List.not_mem_nil,IsEmpty.forall_iff,forall_const,ite_true]
    exact (positive_below_projection (B a) P (hB a) hP (by rw [← hs]; exact positive_sum_erase B hB a)).2
  | cons k ks ih =>
    rw [intersection,mul_assoc,ih]
    by_cases ht : ∀ l ∈ ks,f l a=v l
    · rw [if_pos ht,coarse_action B (f k) (v k) P hP hB hs (hp k)]
      simp only [List.forall_mem_cons,and_iff_left ht]
    · simp [ht]

theorem intersection_supported {κ : Type} (P : Op) (hP : P*P=P) (C : κ → Op)
    (ks : List κ) : intersection P C ks * P=intersection P C ks := by
  induction ks with
  | nil => exact hP
  | cons k ks ih => rw [intersection,mul_assoc,ih]

/-- Fine-effect uniqueness from a separating family of sharp marginals.
Invalid outcomes may be padded into the same ambient answer type. -/
theorem fine_unique {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (B : ι → Op) (P : Op) (hP : Projection P)
    (hB : ∀ a,Positive (B a)) (hs : ∑ a,B a=P)
    (ok : ι → Prop) [DecidablePred ok] (hz : ∀ a,¬ok a → B a=0)
    (f : κ → ι → Bool) (ks : List κ) (a : ι)
    (hp : ∀ k,Projection (coarse B (f k) (f k a)))
    (ha : ok a)
    (hsep : ∀ b,ok b → (∀ k ∈ ks,f k b=f k a) → b=a) :
    B a=intersection P (fun k => coarse B (f k) (f k a)) ks := by
  have ht := intersection_supported P hP.2 (fun k => coarse B (f k) (f k a)) ks
  have ht' : (∑ b,intersection P (fun k => coarse B (f k) (f k a)) ks * B b)=
      intersection P (fun k => coarse B (f k) (f k a)) ks := by
    rw [← Finset.mul_sum,hs]; exact ht
  clear ht
  rw [← ht']
  have he (b : ι) :
      intersection P (fun k => coarse B (f k) (f k a)) ks * B b=
        if b=a then B a else 0 := by
    rw [intersection_action B P hP hB hs f (fun k => f k a) hp]
    by_cases hb : ok b
    · by_cases he : ∀ k ∈ ks,f k b=f k a
      · have heq := hsep b hb he
        subst b
        simp
      · have hne : b≠a := by intro heq; subst b; exact he (by simp)
        simp [he,hne]
    · have hne : b≠a := by intro heq; exact hb (heq ▸ ha)
      rw [hz b hb]
      simp [hne]
  simp_rw [he]
  simp

#print axioms intersection_action
#print axioms intersection_supported
#print axioms fine_unique
end Sigma2.FiniteJoint



