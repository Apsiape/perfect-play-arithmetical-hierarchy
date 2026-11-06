import Sigma2.TreeFoundation

noncomputable section
open scoped BigOperators
namespace Sigma2.CornerCompression

variable (e : Op) (he : Projection e)
include he

lemma star_commute (A : Op) (hA : e*A=A*e) : e*star A=star A*e := by
  have h := congrArg star hA
  simpa only [star_mul,he.1] using h.symm

lemma mul (A B : Op) (hA : e*A=A*e) : (e*A)*(e*B)=e*(A*B) := by
  calc
    _ = e*(A*e)*B := by noncomm_ring
    _ = e*(e*A)*B := by rw [hA]
    _ = _ := by rw [← mul_assoc e e,he.2,mul_assoc]

lemma compress_star (A : Op) (hA : e*A=A*e) : star (e*A)=e*star A := by
  rw [star_mul,he.1,star_commute e he A hA]

lemma commute_eval (L : ℕ → Op) (hL : ∀ i,e*L i=L i*e) (p : Expr) :
    e*p.eval 1 L=p.eval 1 L*e := by
  induction p with
  | scalar q => simp [Expr.eval,mul_smul_comm,smul_mul_assoc]
  | label i => exact hL i
  | add p q hp hq => simp only [Expr.eval,mul_add,add_mul,hp,hq]
  | mul p q hp hq =>
    change e*(_*_) = (_*_)*e
    rw [← mul_assoc,hp,mul_assoc,hq,mul_assoc]
  | adj p hp => exact star_commute e he _ hp

lemma eval (L : ℕ → Op) (hL : ∀ i,e*L i=L i*e) (p : Expr) :
    p.eval e (fun i => e*L i)=e*p.eval 1 L := by
  induction p with
  | scalar q => simp [Expr.eval,mul_smul_comm]
  | label i => rfl
  | add p q hp hq => simp only [Expr.eval,hp,hq,mul_add]
  | mul p q hp hq =>
    simp only [Expr.eval,hp,hq]
    exact mul e he _ _ (commute_eval e he L hL p)
  | adj p hp =>
    simp only [Expr.eval,hp]
    exact compress_star e he _ (commute_eval e he L hL p)

lemma supported (A : Op) (hA : e*A=A*e) : e*(e*A)=e*A ∧ (e*A)*e=e*A := by
  constructor
  · rw [← mul_assoc,he.2]
  · rw [mul_assoc,← hA,← mul_assoc,he.2]

lemma projection (A : Op) (hA : e*A=A*e) (hp : Projection A) : Projection (e*A) := by
  exact ⟨by rw [compress_star e he A hA,hp.1],by rw [mul e he A A hA,hp.2]⟩

lemma positive (A : Op) (hA : e*A=A*e) (hp : Positive A) : Positive (e*A) := by
  have hh := hp.conj_adjoint e
  change Positive (e*A*star e) at hh
  rw [he.1,(supported e he A hA).2] at hh
  exact hh

lemma typed (A : Op) (hA : e*A=A*e) (t : LabelType) (ht : TypedAt 1 A t) :
    TypedAt e (e*A) t := by
  cases t with
  | unitary =>
    constructor
    · rw [compress_star e he A hA,mul e he (star A) A (star_commute e he A hA),ht.1,mul_one]
    · rw [compress_star e he A hA,mul e he A (star A) hA,ht.2,mul_one]
  | projection => exact projection e he A hA ht
  | positive =>
    refine ⟨positive e he A hA ht.1,?_⟩
    have hc : e*(1-A)=(1-A)*e := by simp only [mul_sub,sub_mul,mul_one,one_mul,hA]
    simpa only [mul_sub,mul_one] using positive e he (1-A) hc ht.2
  | contraction =>
    exact (norm_mul_le _ _).trans (by
      simpa only [one_mul] using mul_le_mul (TreeFoundation.projection_norm_le e he) ht
        (norm_nonneg _) zero_le_one)

#print axioms eval
#print axioms typed
end Sigma2.CornerCompression
